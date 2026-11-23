import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in

theorem isCanonGauge_mapFB_tower {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) {h : PS k 2 d} {R' : Type} [CommRing R'] [Algebra R' k]
    (φ : R →+* R') (hφ : ∀ x, algebraMap R' k (φ x) = algebraMap R k x) (hh : B.IsCanonGauge k h) :
    (FBMap.mapFB φ B).IsCanonGauge k h := by
  have hK : ∀ {n : ℕ} (f : PS R n d), FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
    intro n f
    ext mo
    simp only [MvPowerSeries.coeff_map, hφ]
  have hF : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => hK _
  have hA : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => hK _
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK _).trans hh.ph1
  · rw [hF]; exact (hK _).trans hh.ph2
  · exact (hK _).trans hh.sy
  · rw [hA]; exact (hK _).trans (hh.ad a)

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_formalBiext_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧
      (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧
      B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X
  letI := io.toAlgebra
  obtain ⟨BT, e1, e2, -, -, -, -, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨-, -, h3, h4⟩ := e7 X.C
  refine ⟨FBMap.mapFB X.ι BT, ?_, fun a => ?_,
    isCanonGauge_mapFB_tower BT X.ι (fun x => (X.comp x).symm) ((h3 _).2 h4)⟩
  · rw [← e1]; rfl
  · rw [← e2]; rfl

end GlobalTheory.CharDepth
