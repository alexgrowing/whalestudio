import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
noncomputable section
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
end GlobalTheory.GTwoTheta
namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  intro hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hcrys := _root_.GlobalTheory.CrysFromGTwo.main_alt_alt hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C
  have hamb := GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C
  have hH := twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2
  refine ⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1,
    fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, hH.2⟩, fun x => ?_⟩
  rw [← locC_rTwO]
  exact (hcrys.2 x).2
end GlobalTheory.GTwoTheta
end
end
