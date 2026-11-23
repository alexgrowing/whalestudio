import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagQuotientConnectingMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_quotient_connecting_map : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (l : Fin n) (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback σ).obj E),
    GlobalTheory.VB.IsSubbundle u → GlobalTheory.VB.IsSubbundle v → GlobalTheory.VB.IsVB A₀ l → GlobalTheory.VB.IsVB A₁ (l + 1) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ, e.hom ≫ fl.ι l.succ =
      (Scheme.Modules.pullback ρ).map v ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc, e.hom ≫ fl.ι l.castSucc =
      (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    ∃ M : HermLB q₁, (M.pull ρ wρ).Isometric (VMetric.grLB fl l (H.pull π w)) := by
  first | exact @GlobalTheory.StepLine.isometric_grLB_of_steps_pull | exact GlobalTheory.StepLine.isometric_grLB_of_steps_pull | (intros; apply GlobalTheory.StepLine.isometric_grLB_of_steps_pull <;> assumption)
