import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lt_add_root_neg : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S, GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2)) (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  first | exact @GlobalTheory.SteepSmall.steep_small | exact GlobalTheory.SteepSmall.steep_small | (intros; apply GlobalTheory.SteepSmall.steep_small <;> assumption)
