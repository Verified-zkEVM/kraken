import AdmissionFragment
import CaseSelection

namespace LeanVM.Admission

def stockStubText : Executable :=
  ⟨0x4002f0, [
    ⟨.label "_start", 0⟩,
    ⟨⸨dir| cmpq   $0x2,(%rsp)⸩, 5⟩,
    ⟨⸨dir| jne fail⸩, 6⟩,
    ⟨⸨dir| mov    0x10(%rsp),%rax⸩, 5⟩,
    ⟨⸨dir| movzbl (%rax),%ebx⸩, 3⟩,
    ⟨⸨dir| sub    $0x30,%ebx⸩, 3⟩,
    ⟨⸨dir| cmp    $0xa,%ebx⸩, 3⟩,
    ⟨⸨dir| ja fail⸩, 6⟩,
    ⟨⸨dir| and    $0xfffffffffffffff0,%rsp⸩, 4⟩,
    ⟨⸨dir| mov    $0x9,%eax⸩, 5⟩,
    ⟨⸨dir| mov    $0x20000000,%edi⸩, 5⟩,
    ⟨⸨dir| mov    $0x58000000,%esi⸩, 5⟩,
    ⟨⸨dir| mov    $0x3,%edx⸩, 5⟩,
    ⟨⸨dir| mov    $0x100022,%r10d⸩, 6⟩,
    ⟨⸨dir| mov    $0xffffffffffffffff,%r8⸩, 7⟩,
    ⟨⸨dir| xor    %r9d,%r9d⸩, 3⟩,
    ⟨.byteArray ⟨#[0x0f, 0x05]⟩, 2⟩,
    ⟨⸨dir| cmp    $0x20000000,%rax⸩, 6⟩,
    ⟨⸨dir| jne fail⸩, 6⟩,
    ⟨⸨dir| mov    $0x9,%eax⸩, 5⟩,
    ⟨⸨dir| mov    $0x10000000,%edi⸩, 5⟩,
    ⟨⸨dir| mov    $0x11000,%esi⸩, 5⟩,
    ⟨⸨dir| xor    %edx,%edx⸩, 2⟩,
    ⟨⸨dir| mov    $0x100022,%r10d⸩, 6⟩,
    ⟨⸨dir| mov    $0xffffffffffffffff,%r8⸩, 7⟩,
    ⟨⸨dir| xor    %r9d,%r9d⸩, 3⟩,
    ⟨.byteArray ⟨#[0x0f, 0x05]⟩, 2⟩,
    ⟨⸨dir| cmp    $0x10000000,%rax⸩, 6⟩,
    ⟨⸨dir| jne fail⸩, 6⟩,
    ⟨⸨dir| mov    $0xa,%eax⸩, 5⟩,
    ⟨⸨dir| mov    $0x10001000,%edi⸩, 5⟩,
    ⟨⸨dir| mov    $0x10000,%esi⸩, 5⟩,
    ⟨⸨dir| mov    $0x3,%edx⸩, 5⟩,
    ⟨.byteArray ⟨#[0x0f, 0x05]⟩, 2⟩,
    ⟨⸨dir| test   %rax,%rax⸩, 3⟩,
    ⟨⸨dir| jne fail⸩, 6⟩,
    ⟨⸨dir| mov    $0x10011000,%r13d⸩, 6⟩,
    ⟨⸨dir| lea    -0x8(%r13),%rcx⸩, 4⟩,
    ⟨⸨dir| cmp    $0x10001000,%rcx⸩, 7⟩,
    ⟨⸨dir| jb reject_stack⸩, 6⟩,
    ⟨⸨dir| sub    $0x10001000,%rcx⸩, 7⟩,
    ⟨⸨dir| cmp    $0x4000,%rcx⸩, 7⟩,
    ⟨⸨dir| jb reject_stack⸩, 6⟩
  ] ++ [selectCaseLea, selectCaseShift, selectCaseAdd, selectCaseLength] ++
    stockAdmissionCode.map Prod.snd ++ [
    ⟨⸨dir| cmp    $0x10011000,%rsp⸩, 7⟩,
    ⟨⸨dir| jne reject_abi⸩, 6⟩,
    ⟨⸨dir| movabs $0x1122334455667788,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%rbx⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 6⟩,
    ⟨⸨dir| movabs $0x2233445566778899,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%rbp⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 6⟩,
    ⟨⸨dir| movabs $0x33445566778899aa,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%r12⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 2⟩,
    ⟨⸨dir| movabs $0x445566778899aabb,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%r13⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 2⟩,
    ⟨⸨dir| movabs $0x5566778899aabbcc,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%r14⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 2⟩,
    ⟨⸨dir| movabs $0x66778899aabbccdd,%rax⸩, 10⟩,
    ⟨⸨dir| cmp    %rax,%r15⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 2⟩,
    ⟨⸨dir| lea    0x4b49(%rip),%rdi⸩, 7⟩,
    ⟨⸨dir| mov    0x4b62(%rip),%r12⸩, 7⟩,
    ⟨⸨dir| mov    0x8(%r12),%rcx⸩, 5⟩,
    ⟨⸨dir| cmp    %rcx,(%rdi)⸩, 3⟩,
    ⟨⸨dir| jne reject_abi⸩, 2⟩,
    ⟨⸨dir| cmp    %rcx,0x10(%rdi)⸩, 4⟩,
    ⟨⸨dir| jne fail⸩, 2⟩,
    ⟨⸨dir| mov    0x18(%r12),%rax⸩, 5⟩,
    ⟨⸨dir| cmp    %rax,0x18(%rdi)⸩, 4⟩,
    ⟨⸨dir| jne fail⸩, 2⟩,
    ⟨⸨dir| mov    0x8(%rdi),%rsi⸩, 4⟩,
    ⟨⸨dir| mov    0x10(%r12),%rdi⸩, 5⟩,
    ⟨.byteArray ⟨#[0xf3, 0x48, 0xa7]⟩, 3⟩,
    ⟨⸨dir| jne fail⸩, 2⟩,
    ⟨⸨dir| xor    %edi,%edi⸩, 2⟩,
    ⟨⸨dir| jmp exit⸩, 2⟩,
    ⟨.label "reject_stack", 0⟩,
    ⟨⸨dir| mov    $0x2a,%edi⸩, 5⟩,
    ⟨⸨dir| jmp exit⸩, 2⟩,
    ⟨.label "reject_input", 0⟩,
    ⟨⸨dir| mov    $0x2b,%edi⸩, 5⟩,
    ⟨⸨dir| jmp exit⸩, 2⟩,
    ⟨.label "reject_range", 0⟩,
    ⟨⸨dir| mov    $0x2c,%edi⸩, 5⟩,
    ⟨⸨dir| jmp exit⸩, 2⟩,
    ⟨.label "reject_abi", 0⟩,
    ⟨⸨dir| mov    $0x1,%edi⸩, 5⟩,
    ⟨⸨dir| jmp exit⸩, 2⟩,
    ⟨.label "fail", 0⟩,
    ⟨⸨dir| mov    $0x2,%edi⸩, 5⟩,
    ⟨.label "exit", 0⟩,
    ⟨⸨dir| mov    $0x3c,%eax⸩, 5⟩,
    ⟨.byteArray ⟨#[0x0f, 0x05]⟩, 2⟩
  ]⟩

attribute [local simp] selectCaseLea selectCaseShift selectCaseAdd selectCaseLength
  rangeCmp rangeJae tableLea tableCmp budgetJa

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem stockStubDirectiveAt
    (row : StockAdmissionRow) (member : row ∈ stockAdmissionPlan) :
    stockStubText.directivesAtAddress row.pc = [row.instruction] := by
  have inCode : (row.pc, row.instruction) ∈ stockAdmissionCode := by
    rw [← stockAdmissionPlanCode]
    exact List.mem_map_of_mem member
  generalize row.pc = pc at *
  generalize row.instruction = instr at *
  simp only [stockAdmissionCode, callSetupCode, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at inCode
  rcases inCode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
      stockStubText, stockAdmissionCode, callSetupCode]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem stockStubTextCaseSelectionAt : StockCaseSelectionAt stockStubText := by
  constructor <;> simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
    stockStubText, stockAdmissionCode, callSetupCode]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem stockStubTextAdmissionPlacement (file : List UInt8)
    (slice : ((file.drop 0x3d1).take 120) = stockAdmissionBytes) :
    StockAdmissionPlacement stockStubText (readStockAdmissionFile file) := by
  refine stockAdmissionPlacementOfFile _ file slice stockStubDirectiveAt ?_ ?_
  · change stockStubText.withAddresses.findSome? (fun d =>
      if d.directive = .label "reject_range" then some d.addr else none) = some 0x400501
    simp [Kraken.Executable.withAddresses, stockStubText, stockAdmissionCode, callSetupCode]
  · change stockStubText.withAddresses.findSome? (fun d =>
      if d.directive = .label "reject_input" then some d.addr else none) = some 0x4004fa
    simp [Kraken.Executable.withAddresses, stockStubText, stockAdmissionCode, callSetupCode]

theorem stockAdmissionStepTransfer (file : List UInt8) {fragment loaded : Executable}
    (accepted : stockAdmissionFragmentOfSlice ((file.drop 0x3d1).take 120) = some fragment)
    (loadedAt : StockAdmissionPlacement loaded (readStockAdmissionFile file))
    (row : StockAdmissionRow) (member : row ∈ stockAdmissionPlan)
    (s : MachineData) (next : MachineState → Effects) :
    loaded.step ⟨s, row.pc⟩ next = fragment.step ⟨s, row.pc⟩ next := by
  have fragmentAt := stockAdmissionFragmentPlacement file accepted
  simp only [Executable.step, loadedAt.directiveAt row member, fragmentAt.directiveAt row member]

theorem stockAdmissionLabelTransfer (file : List UInt8) {fragment loaded : Executable}
    (accepted : stockAdmissionFragmentOfSlice ((file.drop 0x3d1).take 120) = some fragment)
    (loadedAt : StockAdmissionPlacement loaded (readStockAdmissionFile file)) :
    loaded.labels.label? "reject_range" = fragment.labels.label? "reject_range" ∧
      loaded.labels.label? "reject_input" = fragment.labels.label? "reject_input" := by
  have fragmentAt := stockAdmissionFragmentPlacement file accepted
  exact ⟨loadedAt.rangeLabel.trans fragmentAt.rangeLabel.symm,
    loadedAt.budgetLabel.trans fragmentAt.budgetLabel.symm⟩

#print axioms stockStubTextCaseSelectionAt
#print axioms stockStubTextAdmissionPlacement
#print axioms stockAdmissionStepTransfer
#print axioms stockAdmissionLabelTransfer

end LeanVM.Admission
