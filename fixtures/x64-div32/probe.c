#define _GNU_SOURCE
#include <cpuid.h>
#include <inttypes.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>

struct registers {
    uint64_t rax;
    uint64_t rdx;
    uint64_t rsi;
};

extern void probe_div32(uint64_t rax, uint64_t rdx, uint64_t rsi, struct registers *out);
extern const unsigned char probe_div32_opcode[];
extern void probe_div64(uint64_t rax, uint64_t rdx, uint64_t rsi, struct registers *out);
extern const unsigned char probe_div64_opcode[];

static void system_failure(const char *operation)
{
    perror(operation);
    exit(EXIT_FAILURE);
}

static void record_cpu(void)
{
    int cpu = sched_getcpu();
    if (cpu < 0)
        system_failure("sched_getcpu");
    if (cpu >= CPU_SETSIZE) {
        fprintf(stderr, "Logical CPU %d is outside the affinity set\n", cpu);
        exit(EXIT_FAILURE);
    }

    cpu_set_t affinity;
    CPU_ZERO(&affinity);
    CPU_SET(cpu, &affinity);
    if (sched_setaffinity(0, sizeof(affinity), &affinity) != 0)
        system_failure("sched_setaffinity");

    unsigned eax, ebx, ecx, edx;
    char vendor[13] = "";
    __cpuid(0, eax, ebx, ecx, edx);
    memcpy(vendor, &ebx, 4);
    memcpy(vendor + 4, &edx, 4);
    memcpy(vendor + 8, &ecx, 4);
    unsigned max_leaf = eax;
    char brand[49] = "";
    if (__get_cpuid_max(0x80000000, NULL) >= 0x80000004) {
        for (unsigned i = 0; i < 3; ++i) {
            unsigned words[4];
            __cpuid(0x80000002 + i, words[0], words[1], words[2], words[3]);
            memcpy(brand + 16 * i, words, sizeof(words));
        }
    }
    __cpuid(1, eax, ebx, ecx, edx);
    printf("cpu=%d vendor=%s brand=%s CPUID.1:EAX=0x%08x\n", cpu, vendor, brand, eax);
    if (max_leaf >= 0x1a && strcmp(vendor, "GenuineIntel") == 0) {
        __cpuid_count(0x1a, 0, eax, ebx, ecx, edx);
        if (eax != 0)
            printf("CPUID.1A:EAX=0x%08x\n", eax);
    }
    char path[128];
    snprintf(path, sizeof(path), "/sys/devices/system/cpu/cpu%d/microcode/version", cpu);
    FILE *revision = fopen(path, "r");
    if (revision != NULL) {
        unsigned version;
        if (fscanf(revision, "%x", &version) == 1)
            printf("microcode=0x%x\n", version);
        fclose(revision);
    }
}

static void expect_divide(const char *case_name, struct registers in, uint32_t quotient, uint32_t remainder)
{
    struct registers out;
    probe_div32(in.rax, in.rdx, in.rsi, &out);
    if (out.rax != quotient || out.rdx != remainder || out.rsi != in.rsi) {
        fprintf(stderr,
                "%s: input RAX=%016" PRIx64 " RDX=%016" PRIx64 " RSI=%016" PRIx64 "\n"
                "got RAX=%016" PRIx64 " RDX=%016" PRIx64 " RSI=%016" PRIx64 "\n"
                "expected RAX=%016" PRIx64 " RDX=%016" PRIx64 " RSI=%016" PRIx64 "\n",
                case_name, in.rax, in.rdx, in.rsi, out.rax, out.rdx, out.rsi,
                (uint64_t)quotient, (uint64_t)remainder, in.rsi);
        exit(EXIT_FAILURE);
    }
}

static void check_general(void)
{
    static const struct {
        const char *name;
        uint32_t eax, edx, esi, quotient, remainder;
    } cases[] = {
        {"zero dividend",           0,          0,              1,          0,          0},
        {"divisor exceeds dividend", 3,          0,              7,          0,          3},
        {"largest quotient",        UINT32_MAX, 0,              1,          UINT32_MAX, 0},
        {"nonzero high dividend",    1,          1,              2,          0x80000000, 1},
        {"high dividend near fault", UINT32_MAX, UINT32_MAX - 1, UINT32_MAX,  UINT32_MAX, UINT32_MAX - 1},
    };
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
        struct registers in = {
            .rax = UINT64_C(0x1111111100000000) | cases[i].eax,
            .rdx = UINT64_C(0x2222222200000000) | cases[i].edx,
            .rsi = UINT64_C(0x3333333300000000) | cases[i].esi,
        };
        expect_divide(cases[i].name, in, cases[i].quotient, cases[i].remainder);
    }
    puts("Passed 5 general cases including full-width register checks");
}

static void check_arena_boundaries(void)
{
    static const uint32_t edge_starts[] = {0x20000000, 0x78000000 - 7};
    for (size_t edge = 0; edge < sizeof(edge_starts) / sizeof(edge_starts[0]); ++edge) {
        for (unsigned offset = 0; offset < 8; ++offset) {
            uint32_t next = edge_starts[edge] + offset;
            struct registers in = {.rax = next, .rdx = 0, .rsi = 8};
            expect_divide("alignment 8", in, next >> 3, next & 7);
        }
    }
    puts("Passed 16 alignment-8 cases near both X1 arena bounds");
}

static void expect_divide64(const char *case_name, struct registers in)
{
    struct registers out;
    probe_div64(in.rax, in.rdx, in.rsi, &out);

    unsigned __int128 dividend = ((unsigned __int128)in.rdx << 64) | in.rax;
    unsigned __int128 recomposed = (unsigned __int128)out.rax * in.rsi + out.rdx;
    if (recomposed != dividend || out.rdx >= in.rsi || out.rsi != in.rsi) {
        fprintf(stderr,
                "%s: input RAX=%016" PRIx64 " RDX=%016" PRIx64 " RSI=%016" PRIx64 "\n"
                "got RAX=%016" PRIx64 " RDX=%016" PRIx64 " RSI=%016" PRIx64 "\n",
                case_name, in.rax, in.rdx, in.rsi, out.rax, out.rdx, out.rsi);
        exit(EXIT_FAILURE);
    }
}

static void check_div64_results(void)
{
    expect_divide64("nonzero high dividend", (struct registers){.rax = 1, .rdx = 1, .rsi = 2});
    expect_divide64("high dividend near fault",
                    (struct registers){.rax = UINT64_MAX, .rdx = UINT64_MAX - 1, .rsi = UINT64_MAX});
    puts("Passed 2 general div rsi cases with nonzero high dividend words");
    for (uint64_t n = 21; n <= 96; ++n) {
        struct registers in = {.rax = UINT64_C(1) << 62, .rdx = 0, .rsi = n};
        expect_divide64("sort length", in);
    }
    puts("Passed div rsi cases for all 76 sort lengths from 21 through 96");
}

static void check_signal(const unsigned char *opcode, int signal, siginfo_t *info, void *raw_context)
{
    const ucontext_t *context = raw_context;
    uintptr_t rip = (uintptr_t)context->uc_mcontext.gregs[REG_RIP];
    _exit(signal == SIGFPE && info->si_code == FPE_INTDIV && rip == (uintptr_t)opcode ? 0 : 2);
}

static void handle_div32_fault(int signal, siginfo_t *info, void *context)
{
    check_signal(probe_div32_opcode, signal, info, context);
}

static void handle_div64_fault(int signal, siginfo_t *info, void *context)
{
    check_signal(probe_div64_opcode, signal, info, context);
}

typedef void (*div_probe)(uint64_t, uint64_t, uint64_t, struct registers *);
typedef void (*fault_handler)(int, siginfo_t *, void *);

static void expect_fault(const char *case_name, div_probe probe, fault_handler handle, struct registers in)
{
    pid_t child = fork();
    if (child < 0)
        system_failure("fork");
    if (child == 0) {
        struct rlimit no_core = {0, 0};
        struct sigaction action = {.sa_sigaction = handle, .sa_flags = SA_SIGINFO};
        sigset_t unblocked;
        if (setrlimit(RLIMIT_CORE, &no_core) != 0 ||
            sigemptyset(&action.sa_mask) != 0 ||
            sigemptyset(&unblocked) != 0 ||
            sigaddset(&unblocked, SIGFPE) != 0 ||
            sigprocmask(SIG_UNBLOCK, &unblocked, NULL) != 0 ||
            sigaction(SIGFPE, &action, NULL) != 0)
            _exit(3);

        struct registers out;
        probe(in.rax, in.rdx, in.rsi, &out);
        _exit(1);
    }

    int status;
    if (waitpid(child, &status, 0) != child)
        system_failure("waitpid");
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        fprintf(stderr, "%s: expected FPE_INTDIV at the DIV instruction, wait status=0x%x\n",
                case_name, (unsigned)status);
        exit(EXIT_FAILURE);
    }
    printf("%s: observed SIGFPE (FPE_INTDIV) at the DIV instruction\n", case_name);
}

int main(void)
{
    if (memcmp(probe_div32_opcode, "\xf7\xf6", 2) != 0) {
        fputs("Expected the f7 f6 encoding for div esi\n", stderr);
        return EXIT_FAILURE;
    }
    if (memcmp(probe_div64_opcode, "\x48\xf7\xf6", 3) != 0) {
        fputs("Expected the 48 f7 f6 encoding for div rsi\n", stderr);
        return EXIT_FAILURE;
    }
    puts("encoding=f7 f6 (div esi)");
    puts("encoding=48 f7 f6 (div rsi)");
    record_cpu();
    check_general();
    check_arena_boundaries();
    check_div64_results();
    expect_fault("div esi zero divisor", probe_div32, handle_div32_fault,
                 (struct registers){.rax = 1, .rdx = 0, .rsi = UINT64_C(1) << 32});
    expect_fault("div esi quotient overflow", probe_div32, handle_div32_fault,
                 (struct registers){.rax = 0, .rdx = 1, .rsi = 1});
    expect_fault("div rsi zero divisor", probe_div64, handle_div64_fault,
                 (struct registers){.rax = 1, .rdx = 0, .rsi = 0});
    expect_fault("div rsi quotient overflow", probe_div64, handle_div64_fault,
                 (struct registers){.rax = 0, .rdx = 1, .rsi = 1});
}
