import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.OfInputs
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.IsQg

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GalCut GlobalTheory.RoadU

namespace UpperTheory.Gal.ToralGalois

structure Inq : Prop extends UpperTheory.Gal.Int.Inp.Inp where
  chl : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLift π P → CharLift π P

end UpperTheory.Gal.ToralGalois
