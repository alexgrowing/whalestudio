import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical
open scoped Pointwise

namespace GlobalTheory.EigenGenerator

theorem norm_le_one_of_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_map_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) (a : 𝓞 E) :
    ‖ρ (a : E)‖ ≤ 1 := norm_le_one_of_int (map_isIntegral_int ρ a.isIntegral_coe)

def primeOf {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) : Ideal (𝓞 E) where
  carrier := {a | ‖ρ (a : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_map_le_one ρ c) (norm_nonneg _) ha

theorem mem_primeOf {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) (a : 𝓞 E) :
    a ∈ primeOf ρ ↔ ‖ρ (a : E)‖ < 1 := Iff.rfl

instance primeOf_isPrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_primeOf]; simp
  · intro a b hab
    rw [mem_primeOf, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    rw [mem_primeOf, mem_primeOf, not_lt, not_lt] at hcon
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hcon.1 hcon.2))

theorem norm_natCast_eq {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']

theorem natCast_mem_primeOf' {E : Type} [Field E] {l : ℕ} [hl : Fact l.Prime] (ρ : E →+* ℂ_[l]) : (l : 𝓞 E) ∈ primeOf ρ := by
  rw [mem_primeOf, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, norm_natCast_eq]
  exact Padic.norm_p_lt_one

variable (D : D7) {l : ℕ} [hl : Fact l.Prime]

theorem norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (ρ : D.host.E →+* ℂ_[l]) {a : D.host.E}
    (ha : a ∈ D.host.AA0) : ‖ρ a‖ ≤ 1 := by
  have hnot : ¬ D.host.𝔟 ≤ primeOf ρ :=
    UpperTheory.Ram.half_not_le D.host _ (UpperTheory.Ram.QSq_notMem D.host (Ideal.IsPrime.ne_top inferInstance) hl.out h2 hq
      (natCast_mem_primeOf' ρ))
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have h1 : 1 ≤ ‖ρ (z : D.host.E)‖ := not_lt.1 hzP
  have h3 : ‖ρ a‖ * ‖ρ (z : D.host.E)‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul]
    have := norm_map_le_one ρ w
    rwa [RingOfIntegers.coe_eq_algebraMap, hw] at this
  exact (le_mul_of_one_le_right (norm_nonneg _) h1).trans h3

theorem exists_sep (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) :
    ∃ x : 𝓞 D.host.E, 1 ≤ ‖rhoH D lam τ x - rhoH D lam τ' x‖ := by
  by_contra hcon
  push Not at hcon
  set σ : D.host.E ≃ₐ[D.host.K] D.host.E :=
    (GlobalTheory.InducedType.galK D.host (D.eTau τ))⁻¹ * GlobalTheory.InducedType.galK D.host (D.eTau τ') with hσ
  have hρ : ∀ x, rhoH D lam τ (σ x) = rhoH D lam τ' x := by
    intro x
    rw [rhoH_apply, rhoH_apply]
    congr 1
    change D.host.φ₀ (GlobalTheory.InducedType.galK D.host (D.eTau τ) (σ x)) =
      D.host.φ₀ (GlobalTheory.InducedType.galK D.host (D.eTau τ') x)
    rw [← AlgEquiv.mul_apply, hσ, mul_inv_cancel_left]
  have h1 : σ = 1 := by
    refine UpperTheory.Ram.inertiaK_trivial D.host hl.out h2 hq (primeOf (rhoH D lam τ))
      (natCast_mem_primeOf' _) σ fun x => ?_
    rw [mem_primeOf]
    have : ((σ • x - x : 𝓞 D.host.E) : D.host.E) = σ x - x := rfl
    rw [this, map_sub, hρ, norm_sub_rev]
    exact hcon x
  rw [hσ, inv_mul_eq_one] at h1
  exact hne (D.eTau.injective ((GlobalTheory.InducedType.galK_bijective D.host).1 h1)).symm

variable (M : IntermediateField ℚ ℂ) [NumberField M]

theorem mem_Qbar (s : M) : (s : ℂ) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom M.val

def lamM (lam : Qbar →+* ℂ_[l]) : M →+* ℂ_[l] :=
  lam.comp ((M.val : M →+* ℂ).codRestrict Qbar (mem_Qbar M))

theorem lamM_apply (lam : Qbar →+* ℂ_[l]) (s : M) : lamM M lam s = lamC lam (s : ℂ) := by
  unfold lamC
  rw [dif_pos (mem_Qbar M s)]
  rfl

variable (hM : ∀ τ x, embT D τ x ∈ M)

def embM (τ : D.what₂.Tau) : D.host.E →+* M := (embT D τ).codRestrict M (hM τ)

theorem liftM_eq (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.liftM M (embT D τ x) = embM D M hM τ x := by
  unfold TaylorLogMetric.liftM
  rw [dif_pos (hM τ x)]
  rfl

theorem lamM_embM (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamM M lam (embM D M hM τ x) = rhoH D lam τ x := by
  rw [lamM_apply, rhoH_apply]
  rfl

theorem mul_mem_mmM (x : 𝓞 D.host.E) {v : D.what₂.Tau → M} (hv : v ∈ mmM D M) :
    (fun τ => embM D M hM τ x * v τ) ∈ mmM D M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    refine Submodule.subset_span ⟨x • a, Submodule.smul_mem _ x ha, ?_⟩
    funext τ
    beta_reduce
    rw [liftM_eq D M hM, liftM_eq D M hM, Algebra.smul_def, map_mul]
  | zero =>
    convert (mmM D M).zero_mem using 1
    funext τ
    simp
  | add v w _ _ hv hw =>
    convert (mmM D M).add_mem hv hw using 1
    funext τ
    simp [mul_add]
  | smul c v _ hv =>
    convert (mmM D M).smul_mem c hv using 1
    funext τ
    simp [Algebra.smul_def, mul_left_comm]

include hM in
theorem norm_coord_le (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (τ : D.what₂.Tau)
    {v : D.what₂.Tau → M} (hv : v ∈ mmM D M) : ‖lamM M lam (v τ)‖ ≤ 1 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    simp only
    rw [liftM_eq D M hM, lamM_embM]
    exact norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ ha
  | zero => simp
  | add v w _ _ hv hw =>
    rw [Pi.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv hw)
  | smul c v _ hv =>
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_one₀ (norm_map_le_one _ c) (norm_nonneg _) hv

include hM in
theorem exists_vanishing (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (τ : D.what₂.Tau)
    (S : Finset D.what₂.Tau) (hS : τ ∉ S) :
    ∃ v ∈ mmM D M, (∀ τ' ∈ S, v τ' = 0) ∧ 1 ≤ ‖lamM M lam (v τ)‖ := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨_, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, rfl⟩, by simp, ?_⟩
    beta_reduce
    rw [liftM_eq D M hM]
    simp
  | insert τ' S _ ih =>
    rw [Finset.mem_insert, not_or] at hS
    obtain ⟨v, hv, hv0, hv1⟩ := ih hS.2
    obtain ⟨x, hx⟩ := exists_sep D lam h2 hq (Ne.symm hS.1)
    let c : 𝓞 M := ⟨embM D M hM τ' x, map_isIntegral_int _ x.isIntegral_coe⟩
    have hc : algebraMap (𝓞 M) M c = embM D M hM τ' x := rfl
    refine ⟨_, (mmM D M).sub_mem (mul_mem_mmM D M hM x hv) ((mmM D M).smul_mem c hv), ?_, ?_⟩
    · intro t ht
      rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, hc]
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact sub_self _
      · simp [hv0 t ht]
    · rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, hc, ← sub_mul, map_mul, map_sub, lamM_embM, lamM_embM,
        norm_mul]
      exact one_le_mul_of_one_le_of_one_le hx hv1

end GlobalTheory.EigenGenerator

open GlobalTheory.EigenGenerator in

theorem GlobalTheory.EigenGenerator.norm_generator_eq_one : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), l ∉ D.host.small → l ≠ D.host.q → ∀ (M : IntermediateField ℚ ℂ) [NumberField M], (∀ τ x, embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), ellT D M τ = Submodule.span (𝓞 M) {s} → ‖lamC lam (s : ℂ)‖ = 1 := by
  intro D l _ lam h2 hq M _ hM τ s hs
  rw [← lamM_apply]
  refine le_antisymm ?_ ?_
  · have h1 : s ∈ ellT D M τ := by rw [hs]; exact Submodule.mem_span_singleton_self s
    have := norm_coord_le D M hM lam h2 hq τ (Submodule.mem_comap.1 h1)
    simpa using this
  · obtain ⟨v, hv, hv0, hv1⟩ := exists_vanishing D M hM lam h2 hq τ (Finset.univ.erase τ) (Finset.notMem_erase _ _)
    have h1 : v τ ∈ ellT D M τ := by
      refine Submodule.mem_comap.2 ?_
      convert hv using 1
      funext t
      by_cases ht : t = τ
      · subst ht; simp
      · rw [hv0 t (Finset.mem_erase.2 ⟨ht, Finset.mem_univ _⟩)]
        simp [ht]
    rw [hs, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    rw [← hc, Algebra.smul_def, map_mul, norm_mul] at hv1
    exact hv1.trans (mul_le_of_le_one_left (norm_nonneg _) (norm_map_le_one _ c))
