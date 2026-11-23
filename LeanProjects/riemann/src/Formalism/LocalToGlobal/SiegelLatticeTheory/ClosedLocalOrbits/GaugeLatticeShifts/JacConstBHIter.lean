import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

def itgF (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (f : Mt k r → ℝ≥0∞) (n m n' : Mt k r) : ℝ≥0∞ :=
  f (fun i j => (Matrix.of n * g * Matrix.of m * (Matrix.of n')⁻¹) i j)

def ItgSwap : Prop :=
  ∀ (k r : ℕ) (νN νb : Measure (Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) νN →
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) νb →
    ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
    (∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2) ∂((νN.prod νN).prod νb)) =
      ∫⁻ n, ∫⁻ m, ∫⁻ n', f (fun i j => (Matrix.of n * g * Matrix.of m * (Matrix.of n')⁻¹) i j) ∂νN ∂νb ∂νN

end Formalism.L2.SG.Pf.BH
