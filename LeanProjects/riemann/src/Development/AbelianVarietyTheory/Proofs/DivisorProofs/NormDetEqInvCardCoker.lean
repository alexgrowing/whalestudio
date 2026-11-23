import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace DetIndexPadic

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {x}) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [Padic.norm_p_pow]

theorem det_ne_zero_of_finite_coker (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T)
    (hc : Nat.card (T ⧸ LinearMap.range φ) ≠ 0) : LinearMap.det φ ≠ 0 := by
  classical
  set n := Nat.card (T ⧸ LinearMap.range φ)
  have hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x := by
    intro x
    have h0 := card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ)
      (x := Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose c hc' using fun i => hk (b i)
  let ψ : T →ₗ[ℤ_[l]] T := b.constr ℤ_[l] c
  have hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id := by
    refine b.ext fun i => ?_
    simp [ψ, hc']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm

theorem norm_det_eq_of_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ),
    Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  intro l _ T _ _ _ _ φ a hcard
  classical
  have hl := (Fact.out : l.Prime)
  have hdet : LinearMap.det φ ≠ 0 := det_ne_zero_of_finite_coker l φ
    (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  set N := LinearMap.range φ with hN
  let e : T ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis ℤ_[l] T
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[l]] N := b'.equiv cb (Equiv.refl _)
  let f : T →ₗ[ℤ_[l]] T := N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)
  have hc : ∀ i, f (b' i) = c i • b' i := by
    intro i
    have : f (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det φ) (LinearMap.det f) at hass
  rw [h1] at hass
  have hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  have hne : ∏ i, c i ≠ 0 := fun h0 => hdet (hass.eq_zero_iff.2 h0)
  obtain ⟨u, hu⟩ := hass
  have h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]
  have h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖ := by
    rw [hcq, Nat.cast_prod, norm_prod, norm_prod]
    exact Finset.prod_congr rfl fun i hi =>
      (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm
  rw [h2, h3, hcard]
  push_cast
  rw [Padic.norm_p_pow]

end DetIndexPadic
end GlobalTheory
