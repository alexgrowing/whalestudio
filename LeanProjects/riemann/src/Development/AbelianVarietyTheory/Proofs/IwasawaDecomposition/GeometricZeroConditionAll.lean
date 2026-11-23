import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAllStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstructedAfterLargeBaseCorePropertyOfForall
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.GeoZeroAt

theorem row_geo0_at : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) S0.GeometricWeakCompatibility := by
  intro hR hL N S Γ hNE hD hT
  have hA := GlobalTheory.T.class_sum_divisor_all hR hL N S Γ hNE hD
  refine AllAtMember.eventually_coreProperty_mono (AllAtMember.forall_linked_bundles_and hA hT) fun Q h => ?_
  exact Row.imp h fun 𝒜 σ _ H _ Fm hc x hx i =>
    let ⟨t⟩ := H.2 Fm hc x hx i
    let ⟨a, b, c, _, e⟩ := H.1 Fm hc x hx i t
    ⟨t, a, b, c, e⟩

end GlobalTheory.Fc.GeoZeroAt
