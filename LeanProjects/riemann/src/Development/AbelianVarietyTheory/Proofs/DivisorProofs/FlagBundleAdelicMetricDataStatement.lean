import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAdelicMetricData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_adelic_metric_data : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} (Yv : ProjVar.Var F) (Bs : Scheme.{0}) (q : Bs ⟶ Sp (𝓞 F))
    (ι : Type) (E : ι → Bs.Modules) (n : ι → ℕ) (h : ∀ a, VMetric q (E a) (n a)) (H : ∀ a, (h a).IsCInf)
    (A : ∀ a, Fin (n a) → TrueGeo.Adl C Yv) (Y₀ : Scheme.{0}) (_ : IsIntegral Y₀) (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (n a)), IsFlagBundle π₀ E n fl₀ →
    ∀ (ar₀ : IsArithVar (π₀ ≫ q) Yv.dim) (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀),
    GlobalTheory.FlagInd.FlagInduces Yv q E n h H A Y₀ π₀ fl₀ ar₀ n₀ →
    ∀ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)),
      IsFlagBundle π E n fl → ∀ (arY : IsArithVar (π ≫ q) Yv.dim) (nY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y),
      GlobalTheory.FlagInd.FlagInduces Yv q E n h H A Y π fl arY nY := by
  first | exact @GlobalTheory.FlagInd.flagInduces_transport | exact GlobalTheory.FlagInd.flagInduces_transport | (intros; apply GlobalTheory.FlagInd.flagInduces_transport <;> assumption)
