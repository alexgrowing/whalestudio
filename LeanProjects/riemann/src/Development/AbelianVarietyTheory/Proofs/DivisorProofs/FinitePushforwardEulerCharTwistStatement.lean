import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePushforwardEulerCharTwist
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pushforward_euler_char_twist : ∀ (k : Type) [Field k] (T T' : Scheme.{0}) [Algebra k Γ(T, ⊤)] [Algebra k Γ(T', ⊤)], IsProjSurface k T → IsProjSurface k T' → ∀ (ρ : T' ⟶ T), ρ ≫ strHom k T = strHom k T' → ∀ (L : LB T'), IsAmpleLB L → ∀ (H : T'.Modules), QCoh.IsFiniteQC H → ∀ᶠ n in atTop, QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) ∧ chi k ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) = chi k (twist H (lbPow L n)) := by
  first | exact @GlobalTheory.PushTwistChi.eventually_isFiniteQC_and_chi_pushforward_twist | exact GlobalTheory.PushTwistChi.eventually_isFiniteQC_and_chi_pushforward_twist | (intros; apply GlobalTheory.PushTwistChi.eventually_isFiniteQC_and_chi_pushforward_twist <;> assumption)
