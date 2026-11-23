import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValueStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem exists_unit_transfQuot_out_eq_smul {F : Type} [Field F] [NumberField F]
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (q : Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F))) :
    ∃ ε : (𝓞 F)ˣ, (_root_.GlobalTheory.HilbFam.transfQuot T q).out = ε • T q.out := by
  have h : _root_.GlobalTheory.HilbFam.transfQuot T q = Quotient.mk _ (T q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [h]
  obtain ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
    (Quotient.mk_out (s := MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) (T q.out)))
  exact ⟨ε, hε.symm⟩

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem gTerm_eq_of_linear_change {F : Type} [Field F] [NumberField F]
    {k : ℕ} (σ : ℂ) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) (x : Fin 2 → F) :
    _root_.GlobalTheory.HilbFam.gTerm k σ b a x =
      ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ)) *
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T x) := by
  unfold _root_.GlobalTheory.HilbFam.gTerm
  simp only [hc, Finset.prod_mul_distrib, norm_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _), mul_inv, mul_pow]
  ring

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_of_linear_change {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} (hk : Even k) {L L' : _root_.GlobalTheory.HilbFam.Lat F}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hL : ∀ x, x ∈ L ↔ T x ∈ L') (hlam : ∀ i, lam i ≠ 0)
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) {G : ℂ}
    (hG : _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G) :
    _root_.GlobalTheory.HilbFam.IsGVal k L b a ((∏ i, lam i)⁻¹ ^ k * G) := by
  have hmem : ∀ q, q ∈ _root_.GlobalTheory.HilbFam.cls L ↔
      _root_.GlobalTheory.HilbFam.transfQuot T q ∈ _root_.GlobalTheory.HilbFam.cls L' := by
    intro q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [_root_.GlobalTheory.HilbFam.cls, Set.mem_setOf_eq, hε]
    have hz : ε • T q.out ≠ 0 ↔ q.out ≠ 0 := by
      constructor
      · intro h h0
        exact h (by rw [h0, map_zero, smul_zero])
      · intro h h0
        apply h
        apply T.injective
        rw [map_zero]
        simpa using congrArg (fun y => ε⁻¹ • y) h0
    rw [Submodule.smul_mem_iff', hz, ← hL]
  let e : _root_.GlobalTheory.HilbFam.cls L ≃ _root_.GlobalTheory.HilbFam.cls L' :=
    (_root_.GlobalTheory.HilbFam.transfQuot T).subtypeEquiv hmem
  have hterm : ∀ (σ : ℂ) (q : _root_.GlobalTheory.HilbFam.cls L),
      _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (e q).1.out =
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T q.1.out) := by
    intro σ q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [e, Equiv.subtypeEquiv_apply]
    rw [hε, _root_.GlobalTheory.HilbFam.gTerm_unit_smul F k σ b' a' ε _ hk]
  have hsum : ∀ (σ G' : ℂ),
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) G' →
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out)
        ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * G') := by
    intro σ G' h
    have h' := (e.hasSum_iff.mpr h).mul_left ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ))
    have hfun : (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out) = fun q ↦
        (∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) *
          ((fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
            _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) ∘ e) q := by
      funext q
      simp only [Function.comp_apply, hterm]
      exact gTerm_eq_of_linear_change σ T hc _
    rw [hfun]
    exact h'
  obtain ⟨h₁, h₂⟩ := hG
  refine ⟨fun hk2 => ?_, fun hk2 => ?_⟩
  · simpa using hsum 0 G (h₁ hk2)
  · subst hk2
    obtain ⟨H, hH, hs, rfl⟩ := h₂ rfl
    have hne : ((‖∏ i, lam i‖ : ℝ) : ℂ) ≠ 0 := by
      simp [Finset.prod_ne_zero_iff, hlam]
    refine ⟨fun σ => (∏ i, lam i)⁻¹ ^ 2 * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * H σ, ?_,
      fun σ hσ => hsum σ _ (hs σ hσ), by simp⟩
    exact (((differentiable_const _).mul
      ((differentiable_id.const_mul (-2 : ℂ)).const_cpow (Or.inl hne))).differentiableOn).mul hH

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.gval_linear_change : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : _root_.GlobalTheory.HilbFam.Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i = lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) → _root_.GlobalTheory.HilbFam.gval k L b a = (∏ i, lam i)⁻¹ ^ k * _root_.GlobalTheory.HilbFam.gval k L' b' a' := by
  intro F _ _ _ k L L' T b a b' a' lam hk hL hlam hc
  by_cases h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G
  · obtain ⟨G, hG⟩ := h
    rw [_root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L' b' a' G hG,
      _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L b a _
        (isGVal_of_linear_change hk T hL hlam hc hG)]
  · have h' : ¬ ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := by
      rintro ⟨G, hG⟩
      refine h ⟨_, isGVal_of_linear_change hk T.symm
        (lam := fun i => (lam i)⁻¹) ?_ (fun i => inv_ne_zero (hlam i)) ?_ hG⟩
      · intro x
        rw [hL (T.symm x), T.apply_symm_apply]
      · intro x i
        rw [hc (T.symm x) i, T.apply_symm_apply, inv_mul_cancel_left₀ (hlam i)]
    rw [_root_.GlobalTheory.HilbFam.gval, dif_neg h', _root_.GlobalTheory.HilbFam.gval, dif_neg h,
      mul_zero]

end GlobalTheory.HilbFam
