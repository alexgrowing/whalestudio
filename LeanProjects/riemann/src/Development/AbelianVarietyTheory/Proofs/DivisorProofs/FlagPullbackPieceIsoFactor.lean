import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.VMetric

theorem isIsometry_pullbackComp_congr {k : Type} [CommRing k] {B Y₀ Y : Scheme.{0}} {p : B ⟶ Sp k}
    (π₀ : Y₀ ⟶ B) (π : Y ⟶ B) {E : B.Modules} {r : ℕ} (h : VMetric p E r) (g' : Y ⟶ Y₀)
    (w : g' ≫ π₀ = π) (hf : g' ≫ π₀ ≫ p = π ≫ p) :
    ((h.pull π₀ rfl).pull g' hf).IsIsometry (h.pull π rfl)
      ((Scheme.Modules.pullbackComp g' π₀).app E ≪≫ (Scheme.Modules.pullbackCongr w).app E) := by
  subst w
  exact IsometryPullback.isIsometry_trans
    ((isIsometry_pull_id_comp k B p E r h).2 Y₀ Y _ _ π₀ g' rfl hf rfl)
    (fun _ _ _ _ _ _ => rfl)

theorem isometric_grLB_of_steps_pull : ∀ {k : Type} [CommRing k] {B Y₀ Y : Scheme.{0}} (p : B ⟶ Sp k) (π₀ : Y₀ ⟶ B)
    (π : Y ⟶ B) (E : B.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf)
    (fl₀ : Vert.Flag ((Scheme.Modules.pullback π₀).obj E) r) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (g' : Y ⟶ Y₀) (w : g' ≫ π₀ = π),
    (∀ i, ∃ e : (Scheme.Modules.pullback g').obj (fl₀.F i) ≅ fl.F i, e.hom ≫ fl.ι i =
      (Scheme.Modules.pullback g').map (fl₀.ι i) ≫ (Scheme.Modules.pullbackComp g' π₀).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) →
    ∀ (hf : g' ≫ π₀ ≫ p = π ≫ p) (i : Fin r),
    (VMetric.grLB fl i (H.pull π rfl)).Isometric ((VMetric.grLB fl₀ i (H.pull π₀ rfl)).pull g' hf) := by
  intro k _ B Y₀ Y p π₀ π E r h H fl₀ fl g' w hs hf i
  have I := isIsometry_pullbackComp_congr π₀ π h g' w hf
  have S (j : Fin (r + 1)) : ((fl₀.pull g').ofIso ((Scheme.Modules.pullbackComp g' π₀).app E ≪≫
      (Scheme.Modules.pullbackCongr w).app E)).SameStep fl j := hs j
  have e₁ := (AdjFlag.step_eq (H.pull π rfl) (S i.castSucc) (S i.succ)).1
  rw [grLB_ofIso I ((H.pull π₀ rfl).pull g' hf) (H.pull π rfl)] at e₁
  exact e₁.symm.trans (isometric_grLB_pull k Y₀ Y _ _ _ r _ (H.pull π₀ rfl) fl₀ g' hf i)

end GlobalTheory.VMetric
