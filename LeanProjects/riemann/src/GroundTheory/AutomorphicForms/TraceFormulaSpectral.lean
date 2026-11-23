import Mathlib
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.UnitaryRepresentations

open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct

namespace GroundTheory.Automorphic

noncomputable section

section Intermediate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem two_mul_traceNorm_comp_le_of_hilbertSchmidt (A : K →L[ℂ] H) (B : H →L[ℂ] K) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]

theorem isTraceClass_comp_of_isHilbertSchmidt {A : K →L[ℂ] H} {B : H →L[ℂ] K}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le_of_hilbertSchmidt A B).trans_lt
    (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h

theorem isTraceClass_and_trace_eq_of_conj (e : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} {S : K →L[ℂ] K}
    (hT : IsTraceClass T) (hS : ∀ v, S (e v) = e (T v)) : IsTraceClass S ∧ trace S = trace T := by
  have hS' : S = ((e : H →L[ℂ] K).comp T).comp (e.symm : K →L[ℂ] H) := by
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp [hS]
  have hSc : IsTraceClass S := by
    obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
    rw [hS', hAB, ← comp_assoc, comp_assoc]
    exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)
  refine ⟨hSc, ?_⟩
  let b := stdHilbertBasis ℂ H
  let b' : HilbertBasis _ ℂ K := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hb' : ∀ i, b' i = e (b i) := fun i => rfl
  have h1 := hSc.hasSum_trace b'
  have h2 := hT.hasSum_trace b
  refine h1.unique (h2.congr_fun fun i => ?_)
  rw [hb', hS, LinearIsometryEquiv.inner_map_map]

end Intermediate

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

section Equiv

variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem Equiv.isTraceClass_integrated_and_trace_eq (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    IsTraceClass (τ.integrated μ f) ∧ trace (τ.integrated μ f) = trace (σ.integrated μ f) := by
  refine isTraceClass_and_trace_eq_of_conj e.toLinearIsometryEquiv h fun v => ?_
  have := comp_integrated_of_mem_intertwiners σ μ e.mem_intertwiners f
  exact (congrArg (fun T : K →L[ℂ] L => T v) this).symm

theorem Equiv.trace_integrated (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    trace (τ.integrated μ f) = trace (σ.integrated μ f) :=
  (e.isTraceClass_integrated_and_trace_eq f h).2

end Equiv

section Decomposition

variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))

theorem integrated_restrict_apply (j : J) (v : V j) :
    (((π.restrict (V j) (hinv j)).integrated μ f v : V j) : H) = π.integrated μ f (v : H) := by
  have := comp_integrated_of_mem_intertwiners (π.restrict (V j) (hinv j)) μ
    (subtypeL_mem_intertwiners π (V j) (hinv j)) f
  exact congrArg (fun T : V j →L[ℂ] H => T v) this

variable {π μ f}

theorem isTraceClass_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) (j : J) :
    IsTraceClass ((π.restrict (V j) (hinv j)).integrated μ f) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
  set ι : V j →L[ℂ] H := (V j).subtypeL
  have hιι : ∀ x : V j, (ι†) (ι x) = x := fun x =>
    ext_inner_left ℂ fun w => by
      rw [adjoint_inner_right]
      rfl
  have heq : (π.restrict (V j) (hinv j)).integrated μ f = ((ι†).comp A).comp (B.comp ι) := by
    ext1 x
    simp only [comp_apply]
    rw [← hιι ((π.restrict (V j) (hinv j)).integrated μ f x)]
    congr 1
    change (((π.restrict (V j) (hinv j)).integrated μ f x : V j) : H) = _
    rw [integrated_restrict_apply, hAB]
    rfl
  rw [heq]
  exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)

variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)

def collectedHilbertBasis : HilbertBasis (Σ j, (exists_hilbertBasis ℂ (V j)).choose) ℂ H :=
  HilbertBasis.mk (v := fun a => (V a.1).subtypeₗᵢ (stdHilbertBasis ℂ (V a.1) a.2))
    (hsum.OrthogonalFamily.orthonormal_sigma_orthonormal fun j =>
      (stdHilbertBasis ℂ (V j)).orthonormal) (by
    refine le_trans (top_le_topologicalClosure_iSup hsum) (Submodule.topologicalClosure_minimal _
      (iSup_le fun j => ?_) (Submodule.isClosed_topologicalClosure _))
    intro v hv
    have hd := (stdHilbertBasis ℂ (V j)).dense_span
    have hmem : (⟨v, hv⟩ : V j) ∈
        (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).topologicalClosure := by
      rw [hd]; trivial
    have h1 := Submodule.topologicalClosure_map (V j).subtypeL
      (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j))))
    have h2 : v ∈ ((Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).map
        ((V j).subtypeL : V j →ₗ[ℂ] H)).topologicalClosure :=
      h1 ⟨⟨v, hv⟩, hmem, rfl⟩
    refine Submodule.topologicalClosure_mono ?_ h2
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨j, i⟩, rfl⟩)

theorem collectedHilbertBasis_apply (a : Σ j, (exists_hilbertBasis ℂ (V j)).choose) :
    collectedHilbertBasis hsum a = ((stdHilbertBasis ℂ (V a.1) a.2 : V a.1) : H) := by
  rw [collectedHilbertBasis, HilbertBasis.coe_mk]
  rfl

include hsum in

theorem hasSum_trace_integrated_restrict (hT : IsTraceClass (π.integrated μ f)) :
    HasSum (fun j => trace ((π.restrict (V j) (hinv j)).integrated μ f))
      (trace (π.integrated μ f)) := by
  have h1 := hT.hasSum_trace (collectedHilbertBasis hsum)
  refine h1.sigma fun j => ?_
  refine ((isTraceClass_integrated_restrict hinv hT j).hasSum_trace
    (stdHilbertBasis ℂ (V j))).congr_fun fun i => ?_
  rw [collectedHilbertBasis_apply, ← integrated_restrict_apply π μ f hinv j]
  rfl

variable (π) in

def restrictSetoid : Setoid J where
  r j k := (π.restrict (V j) (hinv j)).IsEquivalent (π.restrict (V k) (hinv k))
  iseqv := ⟨fun _ => IsEquivalent.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

variable (π) in

def multiplicity (c : Quotient (restrictSetoid π hinv)) : ℕ :=
  Nat.card {j : J // (Quotient.mk (restrictSetoid π hinv) j) = c}

include hsum in

theorem hasSum_multiplicity_mul_trace (hT : IsTraceClass (π.integrated μ f))
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite) :
    HasSum (fun c : Quotient (restrictSetoid π hinv) => (multiplicity π hinv c : ℂ) *
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f))
      (trace (π.integrated μ f)) := by
  set S := restrictSetoid π hinv
  have h0 := hasSum_trace_integrated_restrict hinv hsum hT
  let e := Equiv.sigmaFiberEquiv (Quotient.mk S)
  have h1 : HasSum (fun a : Σ c : Quotient S, {j : J // Quotient.mk S j = c} =>
      trace ((π.restrict (V (e a)) (hinv (e a))).integrated μ f)) (trace (π.integrated μ f)) :=
    (e.hasSum_iff).2 h0
  refine h1.sigma fun c => ?_
  have hfc : Set.Finite {j : J | Quotient.mk S j = c} := by
    refine (hfin c.out).subset fun j hj => ?_
    have : Quotient.mk S j = Quotient.mk S c.out := by rw [show Quotient.mk S j = c from hj]; exact c.out_eq.symm
    exact Quotient.exact this
  have : Finite {j : J // Quotient.mk S j = c} := hfc.to_subtype
  have : Fintype {j : J // Quotient.mk S j = c} := Fintype.ofFinite _
  have hconst : ∀ a : {j : J // Quotient.mk S j = c},
      trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f) =
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f) := by
    intro a
    have hja : Quotient.mk S a.1 = Quotient.mk S c.out := by rw [a.2]; exact c.out_eq.symm
    obtain ⟨eq⟩ := (Quotient.exact hja : S a.1 c.out)
    exact (eq.trace_integrated f (isTraceClass_integrated_restrict hinv hT a.1)).symm
  have h2 := hasSum_fintype (fun a : {j : J // Quotient.mk S j = c} =>
    trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f))
  convert h2 using 1
  rw [Finset.sum_congr rfl fun a _ => hconst a, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    multiplicity, Nat.card_eq_fintype_card]

end Decomposition

end UnitaryRep

end

end GroundTheory.Automorphic
