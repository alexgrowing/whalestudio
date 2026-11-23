import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
def LocalCompatibility (D : D7) (rc : Corr D) : Prop :=
  (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) ∧
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ),
    TamePart μ χ ∧ D.naut.locG (D.naut.muC i) (D.naut.plGw k v) = rc k v 1 (Rep.of (Model.detRep 1 μ)) ∧
    ∀ P : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧
      D.naut.locV i P (D.naut.plGw k v) = rc k v D.R.nV π ∧
      ActsThrough π D.R.r D.R.t χ (D.naut.typeV i P) fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v a)
namespace Loc
section Det
end Det
end Loc
end GlobalTheory.SerSys
end
end
