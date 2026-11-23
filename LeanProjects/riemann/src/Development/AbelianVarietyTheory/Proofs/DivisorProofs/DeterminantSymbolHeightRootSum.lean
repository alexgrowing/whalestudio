import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierRatioLocalNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDecompositionClosedPoint

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DetRefHt

section Local

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Toroidal GlobalTheory.CxPts

theorem lnN_sum {D : D7} (O : Setup D) (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ)
    {ι : Type} [Fintype ι] (n : ι → Letter O.S.Dw → ℤ) :
    lnN (O.met.h0 c σ (∑ i, n i)) (genAt (divOf (O.Φ.C c) (∑ i, n i)) (under z)) z =
      Real.log ‖ratVal (genAt (divOf (O.Φ.C c) (∑ i, n i)) (under z) /
        ∏ i, genAt (divOf (O.Φ.C c) (n i)) (under z)) z‖ +
      ∑ i, lnN (O.met.h0 c σ (n i)) (genAt (divOf (O.Φ.C c) (n i)) (under z)) z := by
  classical
  set A : (O.var c).Fnˣ := ∏ i, eqn (divOf (O.Φ.C c) (n i)) (under z) with hAdef
  have hA : (divOf (O.Φ.C c) (∑ i, n i)).IsEqn (under z) A := GlobalTheory.OmCx.prod_isEqn O c (under z) Finset.univ n
  have k1 : (cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i)) ((cxSt _).cx _ σ ((A : (O.var c).Fn)⁻¹)) z =
      ∏ i, (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
        ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := by
    obtain ⟨xa, P, hc⟩ := h
    rw [hc.h0_eq, ← Units.val_inv_eq_inv_val]
    exact (Var.pn_frame hA).trans ((GlobalTheory.OmCx.prod_h O c σ z (xa.eigMet (embOf O.κ.e σ)) Finset.univ n).trans
      (Finset.prod_congr rfl fun i _ => (Var.pn_frame (Base.isEqn_eqn _ _)).symm))
  have hgen : (divOf (O.Φ.C c) (∑ i, n i)).GeneratesAt (under z) ((A : (O.var c).Fn)⁻¹) :=
    CartierDiv.isEqn_iff_generatesAt_inv.1 hA
  set g := genAt (divOf (O.Φ.C c) (∑ i, n i)) (under z) with hgdef
  have hA0 : (A : (O.var c).Fn) ≠ 0 := Units.ne_zero _
  have hu : UnitAt (under z) (g * (A : (O.var c).Fn)) := by
    have := (Base.isEqn_eqn (divOf (O.Φ.C c) (∑ i, n i)) (under z)).generatesAt_iff.1 hgen
    have e : g * (A : (O.var c).Fn) =
        ((A : (O.var c).Fn)⁻¹ * (eqn (divOf (O.Φ.C c) (∑ i, n i)) (under z) : (O.var c).Fn))⁻¹ := by
      rw [hgdef, genAt, Units.val_inv_eq_inv_val, mul_inv, inv_inv, mul_comm]
    rw [e]
    exact this.inv
  have hg : g = (g * (A : (O.var c).Fn)) * (A : (O.var c).Fn)⁻¹ := by field_simp
  have k2 : (cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i)) ((cxSt _).cx _ σ g) z =
      ‖ratVal (g * (A : (O.var c).Fn)) z‖ ^ 2 *
        (cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i)) ((cxSt _).cx _ σ (A : (O.var c).Fn)⁻¹) z := by
    conv_lhs => rw [hg]
    exact (cxSt _).pn_mul _ σ _ _ _ _ z hu.regAt hgen.regularAt
  have hq : g / ∏ i, genAt (divOf (O.Φ.C c) (n i)) (under z) = g * (A : (O.var c).Fn) := by
    simp [genAt, hAdef, Units.coe_prod, div_eq_mul_inv, Finset.prod_inv_distrib]
  have hpos : ∀ i, 0 < (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
      ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := fun i => h.referenceMetric_posAt c σ (n i) z
  have hr : ratVal (g * (A : (O.var c).Fn)) z ≠ 0 := ratVal_ne_zero hu
  simp only [lnN]
  rw [hq, k2, k1, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hr))
    (Finset.prod_ne_zero_iff.2 fun i _ => (hpos i).ne'), Real.log_pow,
    Real.log_prod fun i _ => (hpos i).ne', ← Finset.sum_div]
  push_cast
  ring

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

open Classical in

theorem lgOf_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Y.Y) :
    lgOf Y (∑ i ∈ s, ρ i) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (∑ i ∈ s, ρ i))) (below y.1))⁻¹ *
        ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) (below y.1)) : Y.Y.Fnˣ) : Y.Y.Fn))) +
      ∑ i ∈ s, lgOf Y (ρ i) v ε y := by
  have hp := LineTest.residueCharacteristic_prime v
  have UW := GlobalTheory.CombInd.Tens.unitAt_prod Y (∑ i ∈ s, ρ i) (below y.1)
  have Ui := fun i => GlobalTheory.CombInd.Tens.unitAt_prod Y (ρ i) (below y.1)
  simp only [lgOf, dif_pos hp]
  rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  have hP : (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (∑ i ∈ s, ρ i) x) =
      (∏ i ∈ s, ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) := by
    rw [GlobalTheory.CovolFin.expo_sum, Finset.prod_comm]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.sum_apply, GlobalTheory.CovolFin.zpow_finsum]
  set U : Y.Y.Fnˣ := (eqn (divOf Y (expo Dw (∑ i ∈ s, ρ i))) b)⁻¹ * ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) b) with hU
  set V : Y.Y.Fnˣ := ∏ i ∈ s, ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) with hV
  have hprod : ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (∑ i ∈ s, ρ i) x) * (eqn (divOf Y (expo Dw (∑ i ∈ s, ρ i))) b)⁻¹) =
      U * V := by
    rw [hU, hV, hP, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    simp only [mul_assoc, mul_left_comm (∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) b)), mul_inv_cancel, mul_one]
    exact mul_comm _ _
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y.1 ε.w s
    (fun i => (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) fun i _ => Ui i
  have UU : UnitAt b (U : Y.Y.Fn) := by
    have h₁ : U = (U * V) * V⁻¹ := by simp
    rw [h₁, ← hprod, Units.val_mul, Units.val_inv_eq_inv_val V]
    exact UnitAt.mul UW Us.inv
  rw [hprod, Units.val_mul U V, SmallSec.valAt_mul UU.regAt Us.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero UU)).ne' (ε.w.pos (SmallSec.valAt_ne_zero Us)).ne', hs,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Free

theorem isComb_sum {D : D7} (O : Setup D) (hO : O.Core) (c : O.s.Comp) {ι : Type} [Fintype ι]
    (ρ : ι → Sym D.host.E →₀ ℤ) :
    IsComb (O.adl0 c (∑ i, ρ i)) (fun i => O.adl0 c (ρ i)) (fun _ => 1) (fun _ _ => 0) := by
  refine ⟨1, fun _ => 1, one_pos, fun i => by simp [Setup.adl0, adlOf], ?_,
    fun σ z => ⟨hO.referenceMetric_posAt c σ _ z, ?_⟩, fun v e y => ?_⟩
  · simp only [one_smul, Setup.adl0, adlOf]
    rw [GlobalTheory.CovolFin.expo_sum, GlobalTheory.OmCx.divOf_sum]
  · have key := lnN_sum O hO c σ z fun i => expo O.S.Dw (ρ i)
    simp only [Nat.cast_one, one_mul, pow_one, mul_zero, sub_zero, Int.cast_one, zpow_one]
    simp only [lnAdl, Setup.adl0, adlOf]
    rw [GlobalTheory.CovolFin.expo_sum]
    simp only [Pi.zero_apply, mul_zero, sub_zero]
    exact key
  · simp only [Nat.cast_one, one_mul, pow_one, Int.cast_one, zpow_one]
    refine (lgOf_sum (O.Φ.C c) Finset.univ ρ v e y).trans ?_
    congr 4
    simp only [Setup.adl0, adlOf, genAt, Units.val_mul, Units.coe_prod, div_eq_mul_inv,
      Finset.prod_inv_distrib, inv_inv, Units.val_inv_eq_inv_val]

end Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

theorem ht_detSym : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (Q : Finset ℕ) (c : O.s.Comp) (τ : D.what₂.Tau) (b : (O.var c).X), IsClosed ({b} : Set (O.var c).X) →
    (O.adl0 c (detSym O.S.Dw (ArIn.ind Q) none (DV.tauEmb D τ))).ht b =
      ∑ r : DV.Rt D.what₂.Tau O.N, (if r.1 = τ then (O.root0 c Q r).ht b else 0) := by
  intro D O hO A T H h Q c τ b hb
  have hd : detSym O.S.Dw (ArIn.ind Q) none (DV.tauEmb D τ) =
      ∑ i : Fin O.N, rootSym O.S.Dw (ArIn.ind Q) none (DV.tauEmb D τ) i := by
    rw [detSym, O.S.rank_eq, Finset.sum_range]
  have e := GlobalTheory.Mean4O.HtComb.main _ _ _ _ _ _ _ _
    (isComb_sum O hO c fun i : Fin O.N => rootSym O.S.Dw (ArIn.ind Q) none (DV.tauEmb D τ) i)
    (fun i y => GlobalTheory.Mean4O.Cover.finite_places_lg_ne_zero _ _ _ _ _ _ _ one_ne_zero
      (GlobalTheory.T.lattice_model_induces_root_metric D O hO.dualRef Q c (h.mdl Q c) Q subset_rfl (τ, i)) y) b hb
  rw [hd, e, Fintype.sum_prod_type, Finset.sum_eq_single τ (fun τ' _ hne => by simp [hne]) (by simp)]
  simp [finsum_zero, Setup.root0]

end GlobalTheory.DetRefHt

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

theorem _root_.GlobalTheory.T.determinant_symbol_height_root_sum : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (Q : Finset ℕ) (c : O.s.Comp) (τ : D.what₂.Tau) (b : (O.var c).X), IsClosed ({b} : Set (O.var c).X) →
    (O.adl0 c (detSym O.S.Dw (ArIn.ind Q) none (DV.tauEmb D τ))).ht b =
      ∑ r : DV.Rt D.what₂.Tau O.N, (if r.1 = τ then (O.root0 c Q r).ht b else 0) := GlobalTheory.DetRefHt.ht_detSym
