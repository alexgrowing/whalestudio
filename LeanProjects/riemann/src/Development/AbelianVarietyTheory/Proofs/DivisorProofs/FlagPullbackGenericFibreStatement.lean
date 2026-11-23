import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pullback_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp (𝓞 F)) (d : ℕ), IsArithVar p d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ (ι : Type) [Fintype ι] (N N' : ι → Y.Modules) (n : ι → ℕ),
    (∀ a, IsVB (N' a) (n a)) → ∀ (u : ∀ a, N a ⟶ N' a) (fl : ∀ a, Vert.Flag (N a) (n a))
      (Gs : Scheme.{0}) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp F), IsPullback jY s p (spMap (algebraMap (𝓞 F) F)) →
    (∀ a, IsIso ((Scheme.Modules.pullback jY).map (u a))) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (ρ : X ⟶ Y) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback ρ).obj (N' a)) (n a)) (j : Gs ⟶ X),
      j ≫ ρ = jY ∧ IsPullback j s (ρ ≫ p) (spMap (algebraMap (𝓞 F) F)) ∧ FlagChain.IsCov p d ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ a, Compat ((Scheme.Modules.pullback ρ).map (u a)) ((fl a).pull ρ) (fl' a) := by
  first | exact @GlobalTheory.FlagExtend.main | exact GlobalTheory.FlagExtend.main | (intros; apply GlobalTheory.FlagExtend.main <;> assumption)
