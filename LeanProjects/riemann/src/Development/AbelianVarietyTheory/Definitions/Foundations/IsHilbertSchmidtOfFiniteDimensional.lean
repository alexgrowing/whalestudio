import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise

noncomputable section

namespace GlobalTheory.OpTrace

section Hilbert

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}

variable (H) in

def stdIndex : Set H := (exists_hilbertBasis ℂ H).choose

variable (H) in

def stdBasis : HilbertBasis (stdIndex H) ℂ H := (exists_hilbertBasis ℂ H).choose_spec.choose

def IsHilbertSchmidt (T : H →L[ℂ] K) : Prop :=
  Summable fun i => ‖T (stdBasis H i)‖ ^ 2

def hsNormSq (T : H →L[ℂ] K) : ℝ := ∑' i, ‖T (stdBasis H i)‖ ^ 2

def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (n : ℕ) (B C : Fin n → (H →L[ℂ] H)),
    (∀ i, IsHilbertSchmidt (B i)) ∧ (∀ i, IsHilbertSchmidt (C i)) ∧ T = ∑ i, B i ∘L C i

def trace (T : H →L[ℂ] H) : ℂ := ∑' i, ⟪stdBasis H i, T (stdBasis H i)⟫_ℂ

def HasTrace (T : H →L[ℂ] H) (c : ℂ) : Prop := IsTraceClass T ∧ trace T = c

omit [CompleteSpace H] in

theorem hasSum_norm_inner_sq (e : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖⟪e i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr x)
  simpa [e.repr_apply_apply] using h

omit [CompleteSpace H] [CompleteSpace K] in

theorem summable_matrix (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K}
    (h : Summable fun i => ‖T (e i)‖ ^ 2) :
    Summable fun p : ι × κ => ‖⟪f p.2, T (e p.1)⟫_ℂ‖ ^ 2 := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨fun i => (hasSum_norm_inner_sq f (T (e i))).summable, ?_⟩
  simpa only [(hasSum_norm_inner_sq f _).tsum_eq] using h

theorem hasSum_adjoint (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖adjoint T (f j)‖ ^ 2) s := by
  have hF := (summable_matrix e f h.summable).hasSum
  have hs := h.unique (hF.prod_fiberwise fun i => hasSum_norm_inner_sq f (T (e i)))
  rw [← hs, ← (Equiv.prodComm κ ι).hasSum_iff] at hF
  refine hF.prod_fiberwise fun j => ?_
  have := hasSum_norm_inner_sq e (adjoint T (f j))
  simp only [adjoint_inner_right] at this
  simpa [Function.comp_def, norm_inner_symm (T _)] using this

theorem hasSum_basis (e : HilbertBasis ι ℂ H) (e' : HilbertBasis κ ℂ H) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖T (e' j)‖ ^ 2) s := by
  simpa using hasSum_adjoint (stdBasis K) e' (hasSum_adjoint e (stdBasis K) h)

theorem isHilbertSchmidt_iff (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] K} :
    IsHilbertSchmidt T ↔ Summable fun i => ‖T (e i)‖ ^ 2 :=
  ⟨fun h => (hasSum_basis _ e h.hasSum).summable, fun h => (hasSum_basis e _ h.hasSum).summable⟩

theorem IsHilbertSchmidt.hasSum {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖T (e i)‖ ^ 2) (hsNormSq T) :=
  hasSum_basis _ e (Summable.hasSum h)

theorem IsHilbertSchmidt.adjoint {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) :
    IsHilbertSchmidt (adjoint T) :=
  (hasSum_adjoint _ _ (Summable.hasSum h)).summable

omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.of_norm_le {T : H →L[ℂ] K} {S : H →L[ℂ] L} (h : IsHilbertSchmidt T)
    (c : ℝ) (hS : ∀ x, ‖S x‖ ≤ c * ‖T x‖) : IsHilbertSchmidt S := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) (Summable.mul_left (c ^ 2) h)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hS _) 2

omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.comp_left {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : K →L[ℂ] L) :
    IsHilbertSchmidt (A ∘L T) :=
  h.of_norm_le ‖A‖ fun x => A.le_opNorm _

theorem IsHilbertSchmidt.comp_right {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : L →L[ℂ] H) :
    IsHilbertSchmidt (T ∘L A) := by
  simpa using (h.adjoint.comp_left (ContinuousLinearMap.adjoint A)).adjoint

omit [CompleteSpace K] in

theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] K) := by
  simp [IsHilbertSchmidt, summable_zero]

omit [CompleteSpace K] in

theorem IsHilbertSchmidt.add {S T : H →L[ℂ] K} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
    ((Summable.add hS hT).mul_left 2)
  have h1 := norm_add_le (S (stdBasis H i)) (T (stdBasis H i))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [add_apply]
  nlinarith [sq_nonneg (‖S (stdBasis H i)‖ - ‖T (stdBasis H i)‖)]

omit [CompleteSpace K] in

theorem IsHilbertSchmidt.smul {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (c : ℂ) :
    IsHilbertSchmidt (c • T) :=
  h.of_norm_le ‖c‖ fun x => by simp [norm_smul]

omit [CompleteSpace K] in

theorem isHilbertSchmidt_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] K) :
    IsHilbertSchmidt T := by
  have : Finite (stdIndex H) := (stdBasis H).orthonormal.linearIndependent.finite
  exact Summable.of_finite

theorem exists_hasSum_comp (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    ∃ s : ℂ, HasSum (fun i => ⟪e i, B (C (e i))⟫_ℂ) s ∧ HasSum (fun j => ⟪f j, C (B (f j))⟫_ℂ) s := by
  have h1 := summable_matrix e f ((isHilbertSchmidt_iff e).1 hC)
  have h2 := (Equiv.prodComm ι κ).summable_iff.2 (summable_matrix f e ((isHilbertSchmidt_iff f).1 hB))
  have hF : Summable fun p : ι × κ => ⟪e p.1, B (f p.2)⟫_ℂ * ⟪f p.2, C (e p.1)⟫_ℂ := by
    refine Summable.of_norm_bounded (h1.add h2) fun p => ?_
    simp only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, norm_mul]
    nlinarith [sq_nonneg (‖⟪e p.1, B (f p.2)⟫_ℂ‖ - ‖⟪f p.2, C (e p.1)⟫_ℂ‖),
      mul_nonneg (norm_nonneg ⟪e p.1, B (f p.2)⟫_ℂ) (norm_nonneg ⟪f p.2, C (e p.1)⟫_ℂ)]
  refine ⟨_, hF.hasSum.prod_fiberwise fun i => ?_,
    ((Equiv.prodComm κ ι).hasSum_iff.2 hF.hasSum).prod_fiberwise fun j => ?_⟩
  · simpa only [adjoint_inner_left] using f.hasSum_inner_mul_inner (adjoint B (e i)) (C (e i))
  · have := e.hasSum_inner_mul_inner (adjoint C (f j)) (B (f j))
    simp only [adjoint_inner_left] at this
    simpa [Function.comp_def, mul_comm] using this

theorem hasSum_trace_comp (e : HilbertBasis ι ℂ H)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    HasSum (fun i => ⟪e i, (B ∘L C) (e i)⟫_ℂ) (trace (B ∘L C)) := by
  obtain ⟨s, h1, h2⟩ := exists_hasSum_comp e (stdBasis K) hB hC
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  have : trace (B ∘L C) = s := h3.tsum_eq.trans (h4.unique h2)
  rw [this]; exact h1

theorem trace_comp_comm {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : trace (B ∘L C) = trace (C ∘L B) := by
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  exact h3.tsum_eq.trans h4.tsum_eq.symm

theorem IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪e i, T (e i)⟫_ℂ) (trace T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have key : ∀ {κ : Type _} (f : HilbertBasis κ ℂ H),
      HasSum (fun i => ⟪f i, (∑ k, B k ∘L C k) (f i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := fun f => by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp f (hB k) (hC k)
  have h2 : HasSum (fun i => ⟪e i, (∑ k, B k ∘L C k) (e i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp e (hB k) (hC k)
  rw [show trace (∑ k, B k ∘L C k) = _ from (key (stdBasis H)).tsum_eq]
  exact h2

theorem IsTraceClass.summable_norm {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    Summable fun i => ‖⟪e i, T (e i)⟫_ℂ‖ :=
  (h.hasSum_trace e).summable.norm

omit [CompleteSpace L] in

theorem exists_comp_eq_of_norm_le {C : H →L[ℂ] K} {A : H →L[ℂ] L} (h : ∀ x, ‖C x‖ ≤ ‖A x‖)
    [CompleteSpace L] : ∃ U : L →L[ℂ] K, U ∘L A = C := by
  let M : Submodule ℂ L := (LinearMap.range (A : H →ₗ[ℂ] L)).topologicalClosure
  have hM : ∀ x, A x ∈ M := fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  let a : H →ₗ[ℂ] M := (A : H →ₗ[ℂ] L).codRestrict M hM
  have hd : DenseRange a := by
    rw [DenseRange, Subtype.dense_iff]
    intro y hy
    refine closure_mono ?_ (show y ∈ closure (LinearMap.range (A : H →ₗ[ℂ] L) : Set L) from hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, ⟨x, rfl⟩, rfl⟩
  refine ⟨(C : H →ₗ[ℂ] K).extendOfNorm a ∘L M.orthogonalProjection, ?_⟩
  ext x
  have h1 : M.orthogonalProjection (A x) = a x :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (a x)
  rw [comp_apply, comp_apply, h1]
  exact LinearMap.extendOfNorm_eq hd ⟨1, fun y => by simpa [a] using h y⟩ x

theorem norm_sqrt_apply (C : H →L[ℂ] K) (x : H) :
    ‖(CFC.sqrt (adjoint C ∘L C) : H →L[ℂ] H) x‖ = ‖C x‖ := by
  have hp : (0 : H →L[ℂ] H) ≤ adjoint C ∘L C :=
    (nonneg_iff_isPositive _).2 (isPositive_adjoint_comp_self C)
  set A : H →L[ℂ] H := CFC.sqrt (adjoint C ∘L C)
  have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have h2 : A * A = adjoint C ∘L C := CFC.sqrt_mul_sqrt_self _ hp
  have h3 : ⟪A x, A x⟫_ℂ = ⟪C x, C x⟫_ℂ := by
    rw [← adjoint_inner_right, hA.adjoint_eq, ← adjoint_inner_right C]
    exact congrArg (fun S : H →L[ℂ] H => ⟪x, S x⟫_ℂ) h2
  rw [@norm_eq_sqrt_re_inner ℂ, h3, ← @norm_eq_sqrt_re_inner ℂ]

theorem IsHilbertSchmidt.isTraceClass_comp {B : K →L[ℂ] H} {C : H →L[ℂ] K}
    (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) : IsTraceClass (B ∘L C) := by
  obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (norm_sqrt_apply C x).ge
  refine ⟨1, fun _ => B ∘L U, fun _ => CFC.sqrt (ContinuousLinearMap.adjoint C ∘L C),
    fun _ => hB.comp_right U,
    fun _ => hC.of_norm_le 1 fun x => by rw [norm_sqrt_apply, one_mul], ?_⟩
  rw [Fin.sum_univ_one, comp_assoc, hU]

theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) :=
  ⟨0, fun _ => 0, fun _ => 0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem IsTraceClass.add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := hS
  obtain ⟨m, B', C', hB', hC', rfl⟩ := hT
  refine ⟨n + m, Fin.append B B', Fin.append C C', fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hB, hB']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hC, hC']
  · simp [Fin.sum_univ_add]

theorem isTraceClass_sum {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : IsTraceClass (∑ a ∈ s, T a) :=
  Finset.sum_induction T IsTraceClass (fun _ _ => IsTraceClass.add) isTraceClass_zero h

theorem IsTraceClass.comp_comp {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : IsTraceClass (A ∘L T ∘L A') := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  rw [this]
  exact isTraceClass_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A')

theorem IsTraceClass.comp_left {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (A ∘L T) := by simpa using h.comp_comp A (ContinuousLinearMap.id ℂ H)

theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (T ∘L A) := by simpa using h.comp_comp (ContinuousLinearMap.id ℂ H) A

theorem IsTraceClass.smul {T : H →L[ℂ] H} (h : IsTraceClass T) (c : ℂ) : IsTraceClass (c • T) := by
  simpa using h.comp_left (c • ContinuousLinearMap.id ℂ H)

theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsTraceClass (adjoint T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact ⟨n, fun i => ContinuousLinearMap.adjoint (C i), fun i => ContinuousLinearMap.adjoint (B i),
    fun i => (hC i).adjoint, fun i => (hB i).adjoint, by simp [map_sum]⟩

theorem IsTraceClass.isHilbertSchmidt {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsHilbertSchmidt T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact Finset.sum_induction _ IsHilbertSchmidt (fun _ _ => IsHilbertSchmidt.add)
    isHilbertSchmidt_zero fun i _ => (hC i).comp_left _

@[simp] theorem trace_zero : trace (0 : H →L[ℂ] H) = 0 := by simp [trace]

theorem trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  have := (hS.hasSum_trace (stdBasis H)).add (hT.hasSum_trace (stdBasis H))
  simpa only [trace, add_apply, inner_add_right] using this.tsum_eq

theorem trace_sum {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : trace (∑ a ∈ s, T a) = ∑ a ∈ s, trace (T a) := by
  have := hasSum_sum fun a (ha : a ∈ s) => (h a ha).hasSum_trace (stdBasis H)
  simpa only [trace, ContinuousLinearMap.sum_apply, inner_sum] using this.tsum_eq

theorem trace_smul (c : ℂ) (T : H →L[ℂ] H) : trace (c • T) = c * trace T := by
  simp [trace, inner_smul_right, tsum_mul_left]

theorem IsTraceClass.trace_comp_comp {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : trace (A ∘L T ∘L A') = trace (T ∘L A' ∘L A) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have h1 : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  have h2 : (∑ i, B i ∘L C i) ∘L A' ∘L A = ∑ i, B i ∘L (C i ∘L A' ∘L A) := by
    ext x; simp
  rw [h1, h2, trace_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A'),
    trace_sum _ fun i _ => (hB i).isTraceClass_comp ((hC i).comp_right _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_comp_comm ((hB i).comp_left A) ((hC i).comp_right A'),
    trace_comp_comm (hB i) ((hC i).comp_right _)]
  rfl

theorem IsTraceClass.trace_conj {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H ≃L[ℂ] K) :
    trace ((A : H →L[ℂ] K) ∘L T ∘L (A.symm : K →L[ℂ] H)) = trace T := by
  rw [h.trace_comp_comp]
  congr 1
  ext x; simp

theorem isTraceClass_iff_abs (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} :
    IsTraceClass T ↔ Summable fun i => ⟪e i, CFC.abs T (e i)⟫_ℂ := by
  have hn : ∀ x, ‖CFC.abs T x‖ = ‖T x‖ := norm_sqrt_apply T
  constructor
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).le
    rw [← hU]
    exact ((h.comp_left U).hasSum_trace e).summable
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).ge
    set A : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
    have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    have h2 : A ∘L A = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
    have hHS : IsHilbertSchmidt A := by
      rw [isHilbertSchmidt_iff e]
      refine h.norm.congr fun i => ?_
      rw [← h2, comp_apply, ← adjoint_inner_left, hA.adjoint_eq, inner_self_eq_norm_sq_to_K]
      simp
    rw [← hU, ← h2]
    exact (hHS.isTraceClass_comp hHS).comp_left U

theorem isTraceClass_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    IsTraceClass T := by
  simpa using (isHilbertSchmidt_of_finiteDimensional T).isTraceClass_comp
    (isHilbertSchmidt_of_finiteDimensional (ContinuousLinearMap.id ℂ H))

theorem trace_eq_linearMap_trace [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    trace T = LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  let b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b,
    ← ((isTraceClass_of_finiteDimensional T).hasSum_trace b.toHilbertBasis).tsum_eq, tsum_fintype]
  simp

example (n : ℕ) : HasTrace (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) n :=
  ⟨isTraceClass_of_finiteDimensional _, by simp [trace_eq_linearMap_trace]⟩

example : trace (Complex.I • ContinuousLinearMap.id ℂ ℂ) = Complex.I := by
  simp [trace_smul, trace_eq_linearMap_trace]

end Hilbert

section Unitary

variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

structure IsUnitaryRep (π : G →* (H →L[ℂ] H)) : Prop where

  norm_apply : ∀ g v, ‖π g v‖ = ‖v‖

  continuous_apply : ∀ v, Continuous fun g => π g v

def charRep (χ : G →* Circle) : G →* (ℂ →L[ℂ] ℂ) where
  toFun g := (χ g : ℂ) • ContinuousLinearMap.id ℂ ℂ
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

theorem isUnitaryRep_charRep {χ : G →* Circle} (hχ : Continuous χ) : IsUnitaryRep (charRep χ) :=
  ⟨fun g v => by simp [charRep, Circle.norm_coe], fun v =>
    ((continuous_subtype_val.comp hχ).mul continuous_const : Continuous fun g => (χ g : ℂ) * v)⟩

theorem IsUnitaryRep.inner_apply_left {π : G →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) (g : G)
    (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by
  let U : H →ₗᵢ[ℂ] H := ⟨(π g : H →ₗ[ℂ] H), hπ.norm_apply g⟩
  have h1 : π g (π g⁻¹ w) = w := by
    have : π g * π g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun S : H →L[ℂ] H => S w) this
  conv_lhs => rw [← h1]
  exact U.inner_map_map v (π g⁻¹ w)

variable [MeasurableSpace G]

def IsRepOp (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ v, Integrable (fun g => f g • π g v) μ ∧ T v = ∫ g, f g • π g v ∂μ

open Classical in

def repOp (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) : H →L[ℂ] H :=
  if h : ∃ T, IsRepOp π μ f T then h.choose else 0

def repTrace (π : G →* (H →L[ℂ] H)) (μ : Measure G) (f : G → ℂ) : ℂ := trace (repOp π μ f)

variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}

omit [TopologicalSpace G] [CompleteSpace H] in

theorem IsRepOp.repOp_eq {T : H →L[ℂ] H} (h : IsRepOp π μ f T) : repOp π μ f = T := by
  have h' : ∃ T, IsRepOp π μ f T := ⟨T, h⟩
  ext v
  rw [repOp, dif_pos h', (h'.choose_spec v).2, (h v).2]

omit [CompleteSpace H] in

theorem IsUnitaryRep.isRepOp_of_integrable (hπ : IsUnitaryRep π) (hf : Integrable f μ)
    (hm : ∀ v, AEStronglyMeasurable (fun g => f g • π g v) μ) : IsRepOp π μ f (repOp π μ f) := by
  have hi : ∀ v, Integrable (fun g => f g • π g v) μ := fun v =>
    (hf.norm.mul_const ‖v‖).mono' (hm v) (.of_forall fun g => by simp [norm_smul, hπ.norm_apply])
  let T : H →ₗ[ℂ] H :=
    { toFun := fun v => ∫ g, f g • π g v ∂μ
      map_add' := fun v w => by simp only [map_add, smul_add, integral_add (hi v) (hi w)]
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply, ← integral_smul, smul_comm c] }
  have hT : IsRepOp π μ f (T.mkContinuous (∫ g, ‖f g‖ ∂μ) fun v => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, hπ.norm_apply, integral_mul_const]) := fun v => ⟨hi v, rfl⟩
  rwa [hT.repOp_eq]

variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

omit [CompleteSpace H] in

theorem IsUnitaryRep.isRepOp (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    IsRepOp π μ f (repOp π μ f) :=
  hπ.isRepOp_of_integrable (hf.integrable_of_hasCompactSupport hc) fun v =>
    ((hf.smul (hπ.continuous_apply v)).integrable_of_hasCompactSupport
      hc.smul_right).aestronglyMeasurable

omit [CompleteSpace H] in

theorem IsUnitaryRep.repOp_apply (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (v : H) : repOp π μ f v = ∫ g, f g • π g v ∂μ :=
  (hπ.isRepOp hf hc v).2

theorem IsUnitaryRep.inner_repOp (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (w v : H) :
    ⟪w, repOp π μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  rw [hπ.repOp_apply hf hc, ← integral_inner (hπ.isRepOp hf hc v).1]
  simp only [inner_smul_right]

omit [CompleteSpace H] in

theorem IsUnitaryRep.repOp_add (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : Continuous f') (hc' : HasCompactSupport f') :
    repOp π μ (f + f') = repOp π μ f + repOp π μ f' := by
  refine IsRepOp.repOp_eq fun v => ?_
  obtain ⟨h1, h2⟩ := hπ.isRepOp (μ := μ) hf hc v
  obtain ⟨h3, h4⟩ := hπ.isRepOp (μ := μ) hf' hc' v
  simp only [Pi.add_apply, add_smul, add_apply]
  exact ⟨h1.add h3, by rw [integral_add h1 h3, h2, h4]⟩

omit [CompleteSpace H] in

theorem IsUnitaryRep.repOp_smul (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (c : ℂ) : repOp π μ (c • f) = c • repOp π μ f := by
  refine IsRepOp.repOp_eq fun v => ?_
  obtain ⟨h1, h2⟩ := hπ.isRepOp (μ := μ) hf hc v
  simp only [Pi.smul_apply, smul_assoc, smul_apply]
  exact ⟨h1.smul c, by rw [integral_smul, h2]⟩

theorem IsUnitaryRep.comp_repOp {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H →L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) : A ∘L repOp π μ f = repOp π' μ f ∘L A := by
  ext v
  rw [comp_apply, comp_apply, hπ.repOp_apply hf hc, hπ'.repOp_apply hf hc,
    ← A.integral_comp_comm (hπ.isRepOp hf hc v).1]
  simp only [map_smul, hA]

theorem IsUnitaryRep.repTrace_eq_of_equiv {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H ≃L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) (ht : IsTraceClass (repOp π μ f)) :
    IsTraceClass (repOp π' μ f) ∧ repTrace π' μ f = repTrace π μ f := by
  have h : repOp π' μ f = (A : H →L[ℂ] K) ∘L repOp π μ f ∘L (A.symm : K →L[ℂ] H) := by
    rw [← comp_assoc, hπ.comp_repOp hπ' hf hc (A : H →L[ℂ] K) hA]
    ext v; simp
  rw [repTrace, h]
  exact ⟨ht.comp_comp _ _, ht.trace_conj A⟩

theorem IsUnitaryRep.adjoint_repOp [IsTopologicalGroup G] [BorelSpace G] [μ.IsInvInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    adjoint (repOp π μ f) = repOp π μ fun g => starRingEnd ℂ (f g⁻¹) := by
  have hf' : Continuous fun g => starRingEnd ℂ (f g⁻¹) :=
    Complex.continuous_conj.comp (hf.comp continuous_inv)
  have hc' : HasCompactSupport fun g => starRingEnd ℂ (f g⁻¹) :=
    (hc.comp_homeomorph (Homeomorph.inv G)).comp_left (g := starRingEnd ℂ) (map_zero _)
  ext v
  refine ext_inner_left ℂ fun w => ?_
  rw [adjoint_inner_right, hπ.inner_repOp hf' hc', ← inner_conj_symm, hπ.inner_repOp hf hc,
    ← integral_conj, ← integral_inv_eq_self]
  simp only [map_mul, inner_conj_symm, hπ.inner_apply_left, inv_inv]

theorem IsUnitaryRep.repOp_convolution [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : Continuous f') (hc' : HasCompactSupport f') :
    IsRepOp π μ (fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ) (repOp π μ f ∘L repOp π μ f') := by
  intro v
  have hF : Continuous (Function.uncurry fun x y : G => (f x * f' (x⁻¹ * y)) • π y v) :=
    ((hf.comp continuous_fst).mul (hf'.comp (continuous_fst.inv.mul continuous_snd))).smul
      ((hπ.continuous_apply v).comp continuous_snd)
  have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hc.prod (hc.mul hc')
  have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
      f x * f' (x⁻¹ * y) = 0 := by
    intro x y h
    by_contra hne
    have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
    have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
    exact h ⟨h1, x, h1, _, h2, by simp⟩
  have hFc : HasCompactSupport (Function.uncurry fun x y : G => (f x * f' (x⁻¹ * y)) • π y v) :=
    HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
  have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
    refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
      (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hc ?_ fun y x _ hx => ?_)
    · exact ((hf.comp continuous_snd).mul
        (hf'.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
    HasCompactSupport.intro (hc.mul hc') fun y hy => by
      simp [fun x => h0 x y fun h => hy h.2]
  refine ⟨(hπ.isRepOp hcont hcs v).1, ?_⟩
  simp only [← integral_smul_const]
  rw [← integral_integral_swap_of_hasCompactSupport hF hFc, comp_apply, hπ.repOp_apply hf hc,
    hπ.repOp_apply hf' hc']
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [mul_smul, integral_smul]
  rw [← (π x).integral_comp_comm (hπ.isRepOp hf' hc' v).1,
    ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) • π y v) x]
  simp

theorem repTrace_charRep {χ : G →* Circle} (hχ : Continuous χ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    HasTrace (repOp (charRep χ) μ f) (∫ g, f g * (χ g : ℂ) ∂μ) := by
  have h : repOp (charRep χ) μ f = (∫ g, f g * (χ g : ℂ) ∂μ) • ContinuousLinearMap.id ℂ ℂ := by
    ext
    rw [(isUnitaryRep_charRep hχ).repOp_apply hf hc]
    simp [charRep]
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  rw [h]
  simp [trace_smul, trace_eq_linearMap_trace]

end Unitary

section FiniteRank

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def finRankTrace (T : V →ₗ[ℂ] V) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range T) (T.restrict fun x _ => LinearMap.mem_range_self T x)

theorem finRankTrace_eq (T : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ x, T x ∈ W) :
    finRankTrace T = LinearMap.trace ℂ W (T.restrict fun x _ => hW x) := by
  have hle : LinearMap.range T ≤ W := by rintro _ ⟨x, rfl⟩; exact hW x
  have := Submodule.finiteDimensional_of_le hle
  exact LinearMap.trace_comp_comm' (Submodule.inclusion hle) (T.rangeRestrict ∘ₗ W.subtype)

theorem finRankTrace_add (S T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range S)]
    [FiniteDimensional ℂ (LinearMap.range T)] :
    finRankTrace (S + T) = finRankTrace S + finRankTrace T := by
  have hS : ∀ x, S x ∈ LinearMap.range S ⊔ LinearMap.range T :=
    fun x => Submodule.mem_sup_left (LinearMap.mem_range_self S x)
  have hT : ∀ x, T x ∈ LinearMap.range S ⊔ LinearMap.range T :=
    fun x => Submodule.mem_sup_right (LinearMap.mem_range_self T x)
  rw [finRankTrace_eq S _ hS, finRankTrace_eq T _ hT,
    finRankTrace_eq (S + T) _ fun x => add_mem (hS x) (hT x), ← map_add]
  rfl

theorem finRankTrace_smul (c : ℂ) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finRankTrace (c • T) = c * finRankTrace T := by
  rw [finRankTrace_eq (c • T) (LinearMap.range T)
    fun x => Submodule.smul_mem _ c (LinearMap.mem_range_self T x), finRankTrace, ← smul_eq_mul,
    ← map_smul]
  rfl

theorem finRankTrace_eq_of_equiv {W : Type*} [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    {T : V →ₗ[ℂ] V} {T' : W →ₗ[ℂ] W} (h : ∀ v, e (T v) = T' (e v))
    [FiniteDimensional ℂ (LinearMap.range T)] :
    FiniteDimensional ℂ (LinearMap.range T') ∧ finRankTrace T' = finRankTrace T := by
  have hm : ∀ x ∈ LinearMap.range T, (e : V →ₗ[ℂ] W) x ∈ LinearMap.range T' := by
    rintro _ ⟨v, rfl⟩; exact ⟨e v, (h v).symm⟩
  let a : LinearMap.range T →ₗ[ℂ] LinearMap.range T' := (e : V →ₗ[ℂ] W).restrict hm
  let b : LinearMap.range T' →ₗ[ℂ] LinearMap.range T :=
    T.rangeRestrict ∘ₗ (e.symm : W →ₗ[ℂ] V) ∘ₗ (LinearMap.range T').subtype
  have ha : Function.Surjective a := by
    rintro ⟨_, w, rfl⟩
    exact ⟨⟨T (e.symm w), _, rfl⟩, Subtype.ext (by simpa [a] using h (e.symm w))⟩
  have := Module.Finite.of_surjective a ha
  refine ⟨this, ?_⟩
  have h1 : T'.restrict (fun x _ => LinearMap.mem_range_self T' x) = a ∘ₗ b := by
    ext x; simp [a, b, h]
  have h2 : T.restrict (fun x _ => LinearMap.mem_range_self T x) = b ∘ₗ a := by
    ext x; simp [a, b]
  rw [finRankTrace, finRankTrace, h1, h2, LinearMap.trace_comp_comm']

theorem hasTrace_of_finiteRank {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] :
    HasTrace T (finRankTrace (T : H →ₗ[ℂ] H)) := by
  let R := LinearMap.range (T : H →ₗ[ℂ] H)
  have : CompleteSpace R := FiniteDimensional.complete ℂ R
  let c : H →L[ℂ] R := T.codRestrict R fun x => ⟨x, rfl⟩
  have h := isTraceClass_of_finiteDimensional (ContinuousLinearMap.id ℂ R)
  refine ⟨h.comp_comp R.subtypeL c, (h.trace_comp_comp R.subtypeL c).trans ?_⟩
  rw [trace_eq_linearMap_trace]
  rfl

end FiniteRank

section LocallyConstant

variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]

omit [Module ℂ V] in

theorem finite_range {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    (Set.range F).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => F ⁻¹' {w}) (fun w => hF _)
    fun x _ => Set.mem_iUnion.2 ⟨F x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : F x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport F hx))

variable [MeasurableSpace X]

def lcIntegral (μ : Measure X) (F : X → V) : V := ∑ᶠ w, (μ.real (F ⁻¹' {w}) : ℂ) • w

variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem map_lcIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) (l : V →ₗ[ℂ] E) :
    l (lcIntegral μ F) = ∫ x, l (F x) ∂μ := by
  classical
  have hfin := finite_range hF hc
  have h1 : lcIntegral μ F = ∑ w ∈ hfin.toFinset, (μ.real (F ⁻¹' {w}) : ℂ) • w := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    by_contra hn
    have : F ⁻¹' {w} = ∅ := Set.preimage_singleton_eq_empty.2 (by simpa using hn)
    simp [this] at hw
  have h2 : ∀ x, l (F x) = ∑ w ∈ hfin.toFinset, (F ⁻¹' {w}).indicator (fun _ => l w) x := by
    intro x
    simp [Set.indicator_apply]
  simp only [h1, h2, map_sum, map_smul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_indicator_const _ (hF _).measurableSet, Complex.coe_smul]
  · intro w _
    by_cases hw : w = 0
    · simp [hw]
    · rw [integrable_indicator_iff (hF _).measurableSet]
      refine integrableOn_const (ne_top_of_le_ne_top hc.isCompact.measure_ne_top
        (measure_mono fun x hx => subset_tsupport F ?_))
      rw [Function.mem_support, show F x = w from hx]
      exact hw

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

theorem eq_of_forall_dual {v w : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l v = l w) : v = w := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, h l, sub_self]

end LocallyConstant

section Smooth

open GlobalTheory.PRep

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] in

theorem mem_fixed {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

theorem _root_.GlobalTheory.PRep.IsSmooth.isLocallyConstant_orbit [ContinuousMul G] {ρ : Representation ℂ G V}
    (hρ : IsSmooth ρ) (v : V) : IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {k | ρ k v = v},
    (hρ v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have : ρ g (ρ (g⁻¹ * x) v) = ρ g v := congrArg _ hx
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at this

def leftStabilizer (f : G → ℂ) : Subgroup G where
  carrier := {k | ∀ g, f (k * g) = f g}
  one_mem' := fun g => by rw [one_mul]
  mul_mem' := fun ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left]

theorem isOpen_leftStabilizer [IsTopologicalGroup G] {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : IsOpen (leftStabilizer f : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport f, f (k * g) = f g ∧ f (k⁻¹ * g) = f g := by
    refine hc.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := (hf.comp_continuous (continuous_fst.mul continuous_snd)).eventually_eq ((1 : G), y)
    have h2 := (hf.comp_continuous (continuous_fst.inv.mul continuous_snd)).eventually_eq
      ((1 : G), y)
    have h3 := (hf.comp_continuous (continuous_snd (X := G))).eventually_eq ((1 : G), y)
    filter_upwards [h1, h2, h3] with z a b c
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, one_mul, inv_one] at a b c
    exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h] with k hk g
  by_cases hg : g ∈ tsupport f
  · exact (hk g hg).1
  · by_cases hg' : k * g ∈ tsupport f
    · simpa using (hk _ hg').2.symm
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']

variable [MeasurableSpace G]

open Classical in

def smoothOp (ρ : Representation ℂ G V) (μ : Measure G) (f : G → ℂ) : V →ₗ[ℂ] V :=
  if h : ∃ T : V →ₗ[ℂ] V, ∀ v, T v = lcIntegral μ fun g => f g • ρ g v then h.choose else 0

def smoothTrace (ρ : Representation ℂ G V) (μ : Measure G) (f : G → ℂ) : ℂ :=
  finRankTrace (smoothOp ρ μ f)

variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}

omit [MeasurableSpace G] [BorelSpace G] in

theorem _root_.GlobalTheory.PRep.IsSmooth.smoothOp_integrand (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (v : V) :
    IsLocallyConstant (fun g => f g • ρ g v) ∧ HasCompactSupport fun g => f g • ρ g v :=
  ⟨hf.comp₂ (hρ.isLocallyConstant_orbit v) (· • ·), hc.smul_right⟩

omit [Module ℂ V] in

theorem integrable_map {E : Type*} [NormedAddCommGroup E] {F : G → V} (hF : IsLocallyConstant F)
    (hc : HasCompactSupport F) (l : V → E) (hl : l 0 = 0) : Integrable (fun g => l (F g)) μ :=
  (hF.comp l).continuous.integrable_of_hasCompactSupport (hc.comp_left hl)

theorem _root_.GlobalTheory.PRep.IsSmooth.smoothOp_apply (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (v : V) :
    smoothOp ρ μ f v = lcIntegral μ fun g => f g • ρ g v := by
  have hi := hρ.smoothOp_integrand hf hc
  have h : ∃ T : V →ₗ[ℂ] V, ∀ v, T v = lcIntegral μ fun g => f g • ρ g v := by
    refine ⟨⟨⟨fun v => lcIntegral μ fun g => f g • ρ g v, fun v w => ?_⟩, fun c v => ?_⟩,
      fun _ => rfl⟩
    · refine eq_of_forall_dual fun l => ?_
      rw [map_add l, map_lcIntegral (hi _).1 (hi _).2, map_lcIntegral (hi _).1 (hi _).2,
        map_lcIntegral (hi _).1 (hi _).2, ← integral_add
          (integrable_map (hi _).1 (hi _).2 l l.map_zero)
          (integrable_map (hi _).1 (hi _).2 l l.map_zero)]
      simp only [map_add, smul_add]
    · refine eq_of_forall_dual fun l => ?_
      rw [RingHom.id_apply, map_smul l, map_lcIntegral (hi _).1 (hi _).2,
        map_lcIntegral (hi _).1 (hi _).2, ← integral_smul]
      simp only [map_smul, smul_comm c]
  rw [smoothOp, dif_pos h, h.choose_spec]

theorem _root_.GlobalTheory.PRep.IsSmooth.map_smoothOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hρ : IsSmooth ρ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f)
    (l : V →ₗ[ℂ] E) (v : V) : l (smoothOp ρ μ f v) = ∫ g, f g • l (ρ g v) ∂μ := by
  rw [hρ.smoothOp_apply hf hc, map_lcIntegral (hρ.smoothOp_integrand hf hc v).1 (hρ.smoothOp_integrand hf hc v).2]
  simp only [map_smul]

theorem _root_.GlobalTheory.PRep.IsSmooth.smoothOp_add (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hf' : IsLocallyConstant f') (hc' : HasCompactSupport f') :
    smoothOp ρ μ (f + f') = smoothOp ρ μ f + smoothOp ρ μ f' := by
  ext v
  refine eq_of_forall_dual fun l => ?_
  have h1 := integrable_map (μ := μ) (hρ.smoothOp_integrand hf hc v).1 (hρ.smoothOp_integrand hf hc v).2 l l.map_zero
  have h2 := integrable_map (μ := μ) (hρ.smoothOp_integrand hf' hc' v).1 (hρ.smoothOp_integrand hf' hc' v).2 l
    l.map_zero
  simp only [map_smul] at h1 h2
  rw [LinearMap.add_apply, map_add l, hρ.map_smoothOp (hf.add hf') (hc.add hc'),
    hρ.map_smoothOp hf hc, hρ.map_smoothOp hf' hc', ← integral_add h1 h2]
  simp only [Pi.add_apply, add_smul]

theorem _root_.GlobalTheory.PRep.IsSmooth.smoothOp_smul (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (c : ℂ) : smoothOp ρ μ (c • f) = c • smoothOp ρ μ f := by
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [LinearMap.smul_apply, map_smul l,
    hρ.map_smoothOp (f := c • f) (hf.comp (c • ·)) (hc.comp_left (g := (c • ·)) (smul_zero c)),
    hρ.map_smoothOp hf hc, ← integral_smul]
  simp only [Pi.smul_apply, smul_assoc]

theorem _root_.GlobalTheory.PRep.IsSmooth.map_smoothOp_of_intertwining {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ' : Representation ℂ G W} (hρ : IsSmooth ρ) (hρ' : IsSmooth ρ')
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (j : V →ₗ[ℂ] W)
    (hj : ∀ g v, j (ρ g v) = ρ' g (j v)) (v : V) :
    j (smoothOp ρ μ f v) = smoothOp ρ' μ f (j v) := by
  refine eq_of_forall_dual fun l => ?_
  rw [hρ'.map_smoothOp hf hc]
  simpa [hj] using hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ j) v

theorem _root_.GlobalTheory.PRep.IsSmooth.smoothOp_mem_fixed [μ.IsMulLeftInvariant] (hρ : IsSmooth ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ g, f (k * g) = f g) (v : V) : smoothOp ρ μ f v ∈ fixed ρ K := by
  refine mem_fixed.2 fun k hk => eq_of_forall_dual fun l => ?_
  rw [hρ.map_smoothOp hf hc l, ← integral_mul_left_eq_self _ k]
  simpa [hK k hk] using hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ ρ k) v

theorem _root_.GlobalTheory.PRep.IsAdmissible.finiteDimensional_range_smoothOp [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    FiniteDimensional ℂ (LinearMap.range (smoothOp ρ μ f)) := by
  have h1 := isOpen_leftStabilizer hf hc
  have := hρ.2 (K ⊓ leftStabilizer f) (ho.inter h1)
    (hK.inter_right (Subgroup.isClosed_of_isOpen _ h1))
  refine Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K ⊓ leftStabilizer f)) ?_
  rintro _ ⟨v, rfl⟩
  exact hρ.1.smoothOp_mem_fixed hf hc
    (fun k hk => show k ∈ leftStabilizer f from (Subgroup.mem_inf.1 hk).2) v

theorem _root_.GlobalTheory.PRep.IsAdmissible.smoothTrace_add [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (hf' : IsLocallyConstant f')
    (hc' : HasCompactSupport f') {K : Subgroup G} (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) :
    smoothTrace ρ μ (f + f') = smoothTrace ρ μ f + smoothTrace ρ μ f' := by
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf hc ho hK
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf' hc' ho hK
  rw [smoothTrace, hρ.1.smoothOp_add hf hc hf' hc', finRankTrace_add]
  rfl

theorem _root_.GlobalTheory.PRep.IsAdmissible.smoothTrace_smul [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (c : ℂ) :
    smoothTrace ρ μ (c • f) = c * smoothTrace ρ μ f := by
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf hc ho hK
  rw [smoothTrace, hρ.1.smoothOp_smul hf hc, finRankTrace_smul]
  rfl

theorem _root_.GlobalTheory.PRep.IsAdmissible.smoothTrace_eq_of_equiv [μ.IsMulLeftInvariant] {W : Type} [AddCommGroup W]
    [Module ℂ W] {ρ' : Representation ℂ G W} (hρ : IsAdmissible ρ) (hρ' : IsSmooth ρ')
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (e : V ≃ₗ[ℂ] W)
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) : smoothTrace ρ' μ f = smoothTrace ρ μ f := by
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf hc ho hK
  exact (finRankTrace_eq_of_equiv e
    (hρ.1.map_smoothOp_of_intertwining hρ' hf hc (e : V →ₗ[ℂ] W) he)).2

theorem _root_.GlobalTheory.PRep.IsAdmissible.smoothTrace_indicator [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    smoothTrace ρ μ ((K : Set G).indicator fun _ => 1) =
      μ.real K * Module.finrank ℂ (fixed ρ K) := by
  have hf : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    by_cases hg : g ∈ (K : Set G)
    · exact ⟨K, ho, hg, fun x hx => by simp only [Set.indicator_of_mem, hx, hg]⟩
    · exact ⟨(K : Set G)ᶜ, (K.isClosed_of_isOpen ho).isOpen_compl, hg, fun x hx => by
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  have := hρ.2 K ho hK
  have hm := hρ.1.smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk g => by
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (K.mul_mem hk hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_left hk).1 h)]
  have key : ((smoothOp ρ μ ((K : Set G).indicator fun _ => 1)).restrict fun x _ => hm x :
      fixed ρ K →ₗ[ℂ] fixed ρ K) = (μ.real K : ℂ) • LinearMap.id := by
    ext v
    refine eq_of_forall_dual fun l => ?_
    have h1 : (fun g => (K : Set G).indicator (fun _ => (1 : ℂ)) g • l (ρ g v)) =
        (K : Set G).indicator fun _ => l v := by
      ext g
      by_cases hg : g ∈ (K : Set G)
      · simp [Set.indicator_of_mem hg, mem_fixed.1 v.2 g hg]
      · simp [Set.indicator_of_notMem hg]
    rw [LinearMap.restrict_coe_apply, hρ.1.map_smoothOp hf hc, h1,
      integral_indicator_const _ ho.measurableSet]
    simp
  rw [smoothTrace, finRankTrace_eq _ _ hm, key]
  simp

end Smooth

end GlobalTheory.OpTrace
