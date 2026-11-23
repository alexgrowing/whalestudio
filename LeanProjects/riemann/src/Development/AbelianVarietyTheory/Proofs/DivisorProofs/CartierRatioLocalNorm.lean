import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Toroidal GlobalTheory.CxPts

namespace GlobalTheory.OmCx

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem expo_finset_sum {ι : Type} (s : Finset ι) (w : ι → Sym E →₀ ℤ) :
    expo Dw (∑ i ∈ s, w i) = ∑ i ∈ s, expo Dw (w i) := by
  classical
  funext x
  rw [Finset.sum_apply]
  unfold expo
  rw [Finsupp.sum_finset_sum_index]
  · intro a; simp
  · intro a b₁ b₂; split_ifs <;> simp

end Expo

theorem met_zero_h {D : D7} (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) (G : EigMet O.s.T.Z (embOf O.κ.e σ)) :
    ((O.Φ.C c).met G 0).h 1 z = 1 := by
  have e₃ : Var.val z (1 : (O.Φ.C c).Y.FnC σ) = 1 := by simpa using (Var.val_cx (y := z) 1).trans (Base.ratVal_one _)
  simp [FlagCpt.met, FlagCpt.genSq, prodPow, Var.tv, e₃]

theorem divOf_sum {D : D7} (O : Setup D) (c : O.s.Comp) {ι : Type} (s : Finset ι) (n : ι → Letter O.S.Dw → ℤ) :
    divOf (O.Φ.C c) (∑ i ∈ s, n i) = ∑ i ∈ s, divOf (O.Φ.C c) (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [divOf]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, FlagCpt.divOf_add, ih]

theorem divOf_neg {D : D7} (O : Setup D) (c : O.s.Comp) (n : Letter O.S.Dw → ℤ) :
    divOf (O.Φ.C c) (-n) = -divOf (O.Φ.C c) n := by
  simp [divOf]

theorem prod_isEqn {D : D7} (O : Setup D) (c : O.s.Comp) (x : (O.var c).X) {ι : Type} (s : Finset ι)
    (n : ι → Letter O.S.Dw → ℤ) :
    (divOf (O.Φ.C c) (∑ i ∈ s, n i)).IsEqn x (∏ i ∈ s, eqn (divOf (O.Φ.C c) (n i)) x) := by
  rw [divOf_sum]
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero x
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact (Base.isEqn_eqn _ _).add ih

theorem prod_h {D : D7} (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ)
    (G : EigMet O.s.T.Z (embOf O.κ.e σ)) {ι : Type} (s : Finset ι) (n : ι → Letter O.S.Dw → ℤ) :
    ((O.Φ.C c).met G (∑ i ∈ s, n i)).h (∏ i ∈ s, eqn (divOf (O.Φ.C c) (n i)) (under z)) z =
      ∏ i ∈ s, ((O.Φ.C c).met G (n i)).h (eqn (divOf (O.Φ.C c) (n i)) (under z)) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using met_zero_h O c σ z G
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    rw [FlagCpt.met_add_h (a := eqn (divOf (O.Φ.C c) (n j)) (under z)) G (n j) _ (Base.isEqn_eqn _ _)
      (prod_isEqn O c (under z) s n), ih]

theorem lnN_neg_sum {D : D7} (O : Setup D) (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ)
    {ι : Type} [Fintype ι] (n : ι → Letter O.S.Dw → ℤ) :
    lnN (O.met.h0 c σ (-∑ i, n i)) (genAt (divOf (O.Φ.C c) (-∑ i, n i)) (under z)) z =
      Real.log ‖ratVal (genAt (divOf (O.Φ.C c) (-∑ i, n i)) (under z) /
        ∏ i, genAt (divOf (O.Φ.C c) (n i)) (under z) ^ (-1 : ℤ)) z‖ -
      ∑ i, lnN (O.met.h0 c σ (n i)) (genAt (divOf (O.Φ.C c) (n i)) (under z)) z := by
  classical
  set A : (O.var c).Fnˣ := ∏ i, eqn (divOf (O.Φ.C c) (n i)) (under z) with hAdef
  have hA : (divOf (O.Φ.C c) (∑ i, n i)).IsEqn (under z) A := prod_isEqn O c (under z) Finset.univ n
  have k1 : (cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i)) ((cxSt _).cx _ σ ((A : (O.var c).Fn)⁻¹)) z =
      ∏ i, (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
        ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := by
    obtain ⟨xa, P, hc⟩ := h
    rw [hc.h0_eq, ← Units.val_inv_eq_inv_val]
    exact (Var.pn_frame hA).trans ((prod_h O c σ z (xa.eigMet (embOf O.κ.e σ)) Finset.univ n).trans
      (Finset.prod_congr rfl fun i _ => (Var.pn_frame (Base.isEqn_eqn _ _)).symm))
  have hgen : (divOf (O.Φ.C c) (∑ i, n i)).GeneratesAt (under z) ((A : (O.var c).Fn)⁻¹) :=
    CartierDiv.isEqn_iff_generatesAt_inv.1 hA
  have hdual := h.referenceMetric_mul_dual_eq_one c σ (∑ i, n i) hgen
  rw [inv_inv] at hdual
  have hAN : (divOf (O.Φ.C c) (-∑ i, n i)).GeneratesAt (under z) (A : (O.var c).Fn) := by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 hA.neg
    rw [divOf_neg]
    simpa [Units.val_inv_eq_inv_val] using this
  set g := genAt (divOf (O.Φ.C c) (-∑ i, n i)) (under z) with hgdef
  have hu : UnitAt (under z) (g * (A : (O.var c).Fn)⁻¹) := by
    have := (Base.isEqn_eqn (divOf (O.Φ.C c) (-∑ i, n i)) (under z)).generatesAt_iff.1 hAN
    have e : g * (A : (O.var c).Fn)⁻¹ =
        ((A : (O.var c).Fn) * (eqn (divOf (O.Φ.C c) (-∑ i, n i)) (under z) : (O.var c).Fn))⁻¹ := by
      rw [hgdef, genAt, Units.val_inv_eq_inv_val, mul_inv, mul_comm]
    rw [e]
    exact this.inv
  have hA0 : (A : (O.var c).Fn) ≠ 0 := Units.ne_zero _
  have hg : g = (g * (A : (O.var c).Fn)⁻¹) * A := by field_simp
  have k2 : (cxSt _).pn _ σ _ (O.met.h0 c σ (-∑ i, n i)) ((cxSt _).cx _ σ g) z =
      ‖ratVal (g * (A : (O.var c).Fn)⁻¹) z‖ ^ 2 *
        (cxSt _).pn _ σ _ (O.met.h0 c σ (-∑ i, n i)) ((cxSt _).cx _ σ (A : (O.var c).Fn)) z := by
    conv_lhs => rw [hg]
    exact (cxSt _).pn_mul _ σ _ _ _ _ z hu.regAt hAN.regularAt
  have hq : g / ∏ i, genAt (divOf (O.Φ.C c) (n i)) (under z) ^ (-1 : ℤ) = g * (A : (O.var c).Fn)⁻¹ := by
    simp [genAt, hAdef, Units.coe_prod, div_eq_mul_inv, Finset.prod_inv_distrib]
  have hpos : ∀ i, 0 < (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
      ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := fun i => h.referenceMetric_posAt c σ (n i) z
  have hr : ratVal (g * (A : (O.var c).Fn)⁻¹) z ≠ 0 := ratVal_ne_zero hu
  have hP : (cxSt _).pn _ σ _ (O.met.h0 c σ (-∑ i, n i)) ((cxSt _).cx _ σ (A : (O.var c).Fn)) z =
      ((cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i)) ((cxSt _).cx _ σ ((A : (O.var c).Fn)⁻¹)) z)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdual
  simp only [lnN]
  rw [hq, k2, hP, k1, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hr))
    (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => (hpos i).ne')), Real.log_pow, Real.log_inv,
    Real.log_prod fun i _ => (hpos i).ne', ← Finset.sum_div]
  push_cast
  ring

end GlobalTheory.OmCx

namespace GlobalTheory.OmCx

theorem expo_detOmSym {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (g : ℕ) :
    expo Dw (detOmSym E g) = -∑ k : Fin g, expo Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1) := by
  classical
  unfold detOmSym
  rw [expo_finset_sum, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  funext x
  simp only [wholeSym, expo_single, Pi.neg_apply, Fin.revPerm_apply]
  split_ifs <;> simp

theorem om_cx : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ), lnAdl (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))) σ z = Real.log ‖GlobalTheory.Cartier.ratVal (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (GlobalTheory.Cartier.under z) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (GlobalTheory.Cartier.under z) ^ (-1 : ℤ)) z‖ - ∑ k : Fin (D.R.f * O.N), lnAdl (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)) σ z := by
  intro D O h c σ z
  have he := expo_detOmSym O.S.Dw (D.R.f * O.N)
  have key := lnN_neg_sum O h c σ z fun k : Fin (D.R.f * O.N) =>
    expo O.S.Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)
  simp only [lnAdl, Setup.adl0, adlOf]
  rw [he]
  simp only [Pi.zero_apply, mul_zero, sub_zero]
  exact key

end GlobalTheory.OmCx
