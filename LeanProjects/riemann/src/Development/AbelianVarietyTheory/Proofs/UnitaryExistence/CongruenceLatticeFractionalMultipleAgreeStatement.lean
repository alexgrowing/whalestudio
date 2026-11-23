import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_lattice_fractionalMultiple_agree : ∀ (D : D7) (V : HSp D), ∀ k : GA D V, ((∀ z ∈ latGHat V 1, (finHom V k).1 *ᵥ z ∈ latGHat V 1) ↔ FinCong V 1 k) ∧ ∀ (M : ℕ) (I : Ideal (𝓞 D.host.E)), (∀ b ∈ I, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1 *ᵥ halfVec V b z - halfVec V b z = M • y) ↔ ∀ a ∈ I • latG V 1, ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  first | exact @GlobalTheory.Member.AALev.congruences_agree | exact GlobalTheory.Member.AALev.congruences_agree | (intros; apply GlobalTheory.Member.AALev.congruences_agree <;> assumption)
