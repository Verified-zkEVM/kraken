#define _GNU_SOURCE
#include <cpuid.h>
#include <inttypes.h>
#include <sched.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum {
    CF = 1 << 0,
    PF = 1 << 2,
    AF = 1 << 4,
    ZF = 1 << 6,
    SF = 1 << 7,
    DF = 1 << 10,
    OF = 1 << 11,
    FLAG_MASK = CF | PF | AF | ZF | SF | DF | OF,
    COMMON_MASK = ZF | DF
};

static const struct {
    const char *name;
    unsigned bit;
} flags[] = {
    { "CF", CF }, { "PF", PF }, { "AF", AF }, { "ZF", ZF },
    { "SF", SF }, { "DF", DF }, { "OF", OF }
};

enum { FLAG_COUNT = sizeof(flags) / sizeof(flags[0]) };

struct sample {
    uint64_t dst;
    uint64_t src;
    uint64_t before;
    uint64_t after;
};

extern void probe_bsr(uint64_t src, uint64_t dst, uint64_t seed, struct sample *sample);

struct results {
    unsigned trials;
    unsigned failures;
    unsigned index_parity_mismatches;
    unsigned sd_mismatches[FLAG_COUNT];
    unsigned preserved_mismatches[FLAG_COUNT];
};

static void cpu_profile(int cpu)
{
    unsigned eax, ebx, ecx, edx;
    char vendor[13] = "";
    char brand[49] = "";

    __cpuid(0, eax, ebx, ecx, edx);
    memcpy(vendor, &ebx, 4);
    memcpy(vendor + 4, &edx, 4);
    memcpy(vendor + 8, &ecx, 4);
    unsigned max_basic = eax;
    unsigned max_extended = __get_cpuid_max(0x80000000, NULL);
    if (max_extended >= 0x80000004) {
        for (unsigned i = 0; i < 3; ++i) {
            unsigned words[4];
            __cpuid(0x80000002 + i, words[0], words[1], words[2], words[3]);
            memcpy(brand + 16 * i, words, sizeof(words));
        }
    }
    printf("cpu=%d vendor=%s brand=%s\n", cpu, vendor, brand);
    __cpuid(1, eax, ebx, ecx, edx);
    printf("CPUID.1 eax=%08x ecx=%08x edx=%08x\n", eax, ecx, edx);
    if (max_basic >= 0x1a) {
        __cpuid_count(0x1a, 0, eax, ebx, ecx, edx);
        printf("CPUID.1a eax=%08x\n", eax);
    }
    char path[128];
    snprintf(path, sizeof(path), "/sys/devices/system/cpu/cpu%d/microcode/version", cpu);
    FILE *microcode = fopen(path, "r");
    if (microcode) {
        unsigned revision;
        if (fscanf(microcode, "%x", &revision) == 1)
            printf("microcode=0x%x\n", revision);
        fclose(microcode);
    }
}

static unsigned highest_bit(uint64_t value)
{
    unsigned index = 0;
    for (; (value >>= 1) != 0; ++index)
        ;
    return index;
}

static bool even_popcount(uint64_t value)
{
    bool even = true;
    while (value) {
        value &= value - 1;
        even = !even;
    }
    return even;
}

static unsigned seed_status(unsigned pattern)
{
    unsigned seed = 0;
    for (unsigned i = 0; i < FLAG_COUNT; ++i) {
        if ((pattern >> i) & 1)
            seed |= flags[i].bit;
    }
    return seed;
}

static void test_source(uint64_t src, struct results *results)
{
    static const uint64_t destinations[] = {
        0x7f, UINT64_C(0x123456789abcdef0), UINT64_MAX
    };
    for (unsigned i = 0; i < sizeof(destinations) / sizeof(destinations[0]); ++i) {
        uint64_t dst = destinations[i];
        uint64_t expected_dst = src ? highest_bit(src) : dst;
        for (unsigned pattern = 0; pattern < (1u << FLAG_COUNT); ++pattern) {
            unsigned seed = seed_status(pattern);
            unsigned common = (seed & DF) | (src ? 0 : ZF);
            struct sample sample;
            probe_bsr(src, dst, seed, &sample);
            ++results->trials;
            if (sample.dst != expected_dst || sample.src != src ||
                (sample.before & FLAG_MASK) != seed || (sample.after & COMMON_MASK) != common) {
                if (results->failures++ == 0) {
                    fprintf(stderr,
                            "common behavior mismatch src=%016" PRIx64 " dst=%016" PRIx64
                            " expected_dst=%016" PRIx64 " result=%016" PRIx64
                            " result_src=%016" PRIx64 " seed=%03x before=%03" PRIx64
                            " after=%03" PRIx64 "\n",
                            src, dst, expected_dst, sample.dst, sample.src, seed,
                            sample.before & FLAG_MASK, sample.after & FLAG_MASK);
                }
            }
            unsigned intel_flags = common | (even_popcount(src) ? PF : 0);
            bool index_parity_pf = even_popcount(highest_bit(src));
            results->index_parity_mismatches += ((sample.after & PF) != 0) != index_parity_pf;
            if (i == 0 && pattern == 0 && (src == 0 || src == 1 || src == 3 || src == 4 || src == 7))
                printf("example src=%016" PRIx64 " old_dst=%016" PRIx64
                       " dst=%016" PRIx64 " flags=%03" PRIx64
                       " intel093_flags=%03x\n",
                       src, dst, sample.dst, sample.after & FLAG_MASK, intel_flags);
            unsigned preserved_flags = (seed & ~ZF) | (src ? 0 : ZF);
            for (unsigned j = 0; j < FLAG_COUNT; ++j) {
                unsigned bit = flags[j].bit;
                results->sd_mismatches[j] += ((sample.after ^ intel_flags) & bit) != 0;
                results->preserved_mismatches[j] += ((sample.after ^ preserved_flags) & bit) != 0;
            }
        }
    }
}

int main(void)
{
    int cpu = sched_getcpu();
    if (cpu < 0) {
        perror("sched_getcpu");
        return 1;
    }
    cpu_set_t cpus;
    CPU_ZERO(&cpus);
    CPU_SET(cpu, &cpus);
    if (sched_setaffinity(0, sizeof(cpus), &cpus) != 0) {
        perror("sched_setaffinity");
        return 1;
    }
    cpu_profile(cpu);

    struct results results = {0};
    static const uint64_t edge_sources[] = {
        0, 3, 7, 0x301, UINT64_MAX, UINT64_C(0x8000000000000001),
        UINT64_C(0xaaaaaaaaaaaaaaaa), UINT64_C(0x7fffffffffffffff),
    };
    for (unsigned i = 0; i < sizeof(edge_sources) / sizeof(edge_sources[0]); ++i)
        test_source(edge_sources[i], &results);
    for (unsigned i = 0; i < 64; ++i)
        test_source(UINT64_C(1) << i, &results);

    printf("trials=%u common_behavior_failures=%u\n", results.trials, results.failures);
    puts("flag   Intel 093 mismatches   older-Intel flag-preservation mismatches");
    for (unsigned i = 0; i < FLAG_COUNT; ++i)
        printf("%-4s %22u %42u\n", flags[i].name, results.sd_mismatches[i],
               results.preserved_mismatches[i]);
    printf("PF mismatches against observed hypothesis (even popcount of MSB index, zero indexes to 0)=%u\n",
           results.index_parity_mismatches);
    return results.failures == 0 ? 0 : 1;
}
