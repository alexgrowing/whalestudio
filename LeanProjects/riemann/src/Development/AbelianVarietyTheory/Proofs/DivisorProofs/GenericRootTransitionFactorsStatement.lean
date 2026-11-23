import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRootTransitionFactors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_root_transition_factors : ∀ {X Y₀ : Scheme.{0}} [IsIntegral X] (j : X ⟶ Y₀) {M : Y₀.Modules} {N : ℕ} (fl : Vert.Flag M N) (i : Fin N)
    (r : ((fl.root i).pull j).ι → X.functionFieldˣ),
    (∀ ch ch' : ((fl.root i).pull j).ι, genericPoint X ∈ ((fl.root i).pull j).U ch ⊓ ((fl.root i).pull j).U ch' →
      ∃ (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) (hx : ⊤ ≤ (GlobalTheory.FlagCov.genPt X ≫ j) ⁻¹ᵁ W)
        (lam : Γ(fl.F i.succ, W) → X.functionField),
        (∀ (s : Γ(Y₀, W)) (t : Γ(fl.F i.succ, W)), lam (s • t) = TangentOrigin.evalPt (GlobalTheory.FlagCov.genPt X ≫ j) W hx s * lam t) ∧
        (∃ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0)) ∧
        (∀ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0) →
          lam t = ((r ch)⁻¹ : X.functionFieldˣ)) ∧
        (∀ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_right) ((ch' PUnit.unit).e 0) →
          lam t = ((r ch')⁻¹ : X.functionFieldˣ))) →
    IsRatSec ((fl.root i).pull j) r := by
  first | exact @GlobalTheory.FlagCov.isRatSec_pull_root_of_scaling | exact GlobalTheory.FlagCov.isRatSec_pull_root_of_scaling | (intros; apply GlobalTheory.FlagCov.isRatSec_pull_root_of_scaling <;> assumption)
