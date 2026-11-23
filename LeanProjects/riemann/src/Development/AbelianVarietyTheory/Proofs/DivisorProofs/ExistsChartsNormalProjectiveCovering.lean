import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineIntersectionChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRatioOnChartOverlapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedLineBundleInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBundleSpecialFibreGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedGeneratorIsGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPointGenericFibreStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem exists_glued_bundle : (∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1))) → DensSt → ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) → ∃ D : LB X, D.IsLB ∧ (∃ t : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen) ∧ ∃ sig : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s)).Gen, sig.IsGen ∧ ∀ yb, IsTest p Xw yb → ∀ (y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s), y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : (D.pull yb).Gen) (cc : ℂ_[p]ˣ), e.IsGen → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s D sig yb y e cc → ∀ κ ∈ K yb, ‖(cc : ℂ_[p])‖ = ‖κ‖ := by
  intro ZetaZeros hDens F _ _ V _ p _ hp X s Xw hXi hXn hproj hflat hXw hne K hK h
  have hR : ∀ x y : X, ∃ u, RatioProp h x y u := by
    intro x y
    obtain ⟨A, _, w, a1, a2, hw, h1, h2, hr⟩ :=
      GlobalTheory.T.exists_affine_intersection_charts V X s hproj (cR h x) (cR h y) (cξ h x) (cξ h y) inferInstance inferInstance
    obtain ⟨u, hu1, hu2⟩ := ZetaZeros F V p hp hDens X s Xw hXi hXn hproj hflat hXw hne K hK (cR h x) (cR h y) A (cξ h x)
      (cξ h y) w (cu h x) (cu h y) a1 a2 inferInstance inferInstance hw h1 h2 (c_spec h x).2.2 (c_spec h y).2.2
    exact GlobalTheory.T.unit_ratio_on_chart_overlap p X Xw K h x y A w a1 a2 hw h1 h2 hr u hu1 hu2
  refine ⟨glueLB h, GlobalTheory.T.glued_line_bundle_invertible p X Xw K h hXi hne hXw hR, GlobalTheory.T.glued_bundle_special_fibre_generator F V p hp X s Xw K h hR, sigGen h s,
    GlobalTheory.T.glued_generator_is_generator F V p X s Xw K h hR, ?_⟩
  intro yb hyb y hy e cc _ hco κ hκ
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.local_point_factors_open_immersion 𝓞_ℂ_[p] X (cR h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p]))) (cξ h _) yb inferInstance
    (c_spec h _).2.1
  obtain ⟨ψ, hψ, hn⟩ := GlobalTheory.T.chart_point_generic_fibre F V p X s Xw K h _ φ yb hφ y hy e cc hco
  have hc := (c_spec h _).2.2 φ (by rw [hφ]; exact hyb) ψ hψ κ (by rw [hφ]; exact hκ)
  rw [← hn]
  set a := ψ (cu h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p])) : Localization.Away _)
  have e1 : a = (a - κ) + κ := by ring
  rw [e1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hc.ne, max_eq_right hc.le]

end GlobalTheory.UnitGlue
