import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemInt

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

section Val

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
  {la : HeightOneSpectrum (𝓞 K)} {u : R → EReal}

theorem nonneg_of_idem (hu : IsVal la u) {x : R} (hx : x * x = x) : 0 ≤ u x := by
  have h := hu.mul x x
  rw [hx] at h
  rcases eq_or_ne (u x) ⊤ with h0 | h0
  · rw [h0]
    exact le_top
  · have hr : (((u x).toReal : ℝ) : EReal) = u x := EReal.coe_toReal h0 (hu.ne_bot x)
    rw [← hr] at h ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact EReal.coe_nonneg.mpr (by linarith)

theorem nonneg_smul (hu : IsVal la u) {a : K} (ha : la.valuation K a ≤ 1) {x : R} (hx : 0 ≤ u x) :
    0 ≤ u (a • x) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_smul, hu.zero]
    exact le_top
  · rw [hu.smul a x ha0]
    have hv0 : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hlog : (la.valuation K a).log ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact ha
    refine add_nonneg ?_ hx
    unfold Formalism.BasicNotions.vAdd
    have hn : (0 : ℤ) ≤ -(la.valuation K a).log := neg_nonneg.mpr hlog
    exact_mod_cast hn

theorem nonneg_sum (hu : IsVal la u) {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, 0 ≤ u (x i)) :
    0 ≤ u (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => 0 ≤ u y) (fun a b ha hb => ?_) ?_ hx
  · exact le_trans (le_min ha hb) (hu.add a b)
  · show (0 : EReal) ≤ u 0
    rw [hu.zero]
    exact le_top

end Val

theorem idem_comb_mul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  intro E _ _ _ H Dw l Xo c la m χ v hχ hv f hf u hu
  have hV : IsVal la u := isVal_valSet la u hu
  have h1 : 0 ≤ u (∑ i, v i • χ i) :=
    nonneg_sum hV Finset.univ _ fun i _ => nonneg_smul hV (hv i) (nonneg_of_idem hV (hχ i).2)
  rw [hV.mul]
  exact add_nonneg h1 (hf u hu)

end GlobalTheory.IdemInt
