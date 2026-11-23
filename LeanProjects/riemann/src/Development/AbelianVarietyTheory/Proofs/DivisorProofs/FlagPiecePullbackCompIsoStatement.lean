import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPiecePullbackCompIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_piece_pullback_comp_iso : ∀ {B T Y₁ Y₂ : Scheme.{0}} (g : T ⟶ B) (π₁ : Y₁ ⟶ B) (π₂ : Y₂ ⟶ B) (E : B.Modules)
    (F' : T.Modules) (F₁ : Y₁.Modules) (F₂ : Y₂.Modules) (ι' : F' ⟶ (Scheme.Modules.pullback g).obj E)
    (ι₁ : F₁ ⟶ (Scheme.Modules.pullback π₁).obj E) (ι₂ : F₂ ⟶ (Scheme.Modules.pullback π₂).obj E)
    (g₁ : T ⟶ Y₁) (g₂ : Y₁ ⟶ Y₂) (w₁ : g₁ ≫ π₁ = g) (w₂ : g₂ ≫ π₂ = π₁) (w : (g₁ ≫ g₂) ≫ π₂ = g)
    (e₁ : (Scheme.Modules.pullback g₁).obj F₁ ≅ F'),
    e₁.hom ≫ ι' = (Scheme.Modules.pullback g₁).map ι₁ ≫
      (Scheme.Modules.pullbackComp g₁ π₁).hom.app E ≫ (Scheme.Modules.pullbackCongr w₁).hom.app E →
    ∀ (e₂ : (Scheme.Modules.pullback g₂).obj F₂ ≅ F₁),
    e₂.hom ≫ ι₁ = (Scheme.Modules.pullback g₂).map ι₂ ≫
      (Scheme.Modules.pullbackComp g₂ π₂).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E →
    ∃ e : (Scheme.Modules.pullback (g₁ ≫ g₂)).obj F₂ ≅ F', e.hom ≫ ι' =
      (Scheme.Modules.pullback (g₁ ≫ g₂)).map ι₂ ≫
        (Scheme.Modules.pullbackComp (g₁ ≫ g₂) π₂).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
  first | exact @GlobalTheory.FlagLiftComp.liftComp | exact GlobalTheory.FlagLiftComp.liftComp | (intros; apply GlobalTheory.FlagLiftComp.liftComp <;> assumption)
