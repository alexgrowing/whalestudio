import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.ConstituentConditionAtDistinguishedPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CompatR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
noncomputable section
namespace UpperTheory.GalS
theorem de_rham_points_weight_jumps_alt (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2' : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : UpperTheory.GalC.CutRec D) : (∀ i r, GoodR D.nd i r → G2a D.nd D.naut i r) ∧ DeRhamJumpsDistinctCondition D := by
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  have all : ∀ i r, GoodR D.nd i r → ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i),
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
    intro i r hr x w hw
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hB⟩ := h1 i P
    have hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := by
      have hg : ∀ k, D.nd.l i = D.host.g k → Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := fun k hk => by
        have hw' : w ∈ placesOver D.host.E (D.host.g k) := hk ▸ hw
        rw [hB.2.2.2.1 w (GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw')]
        exact hC i P (by rw [hP]; simp) k w hw'
      by_cases a : D.nd.l i = D.host.g 0
      · exact hg 0 a
      by_cases b : D.nd.l i = D.host.g 1
      · exact hg 1 b
      exact .of_unr (Parts.iso_unr_l D i P Pa w hB hw a b)
    have h := compatR D h0 h2 h5 i r hr x P Pa hP hB w hw hn
    exact ⟨h.1, h.2.2⟩
  exact ⟨fun i r hr => (Parts.crys_unram_of_lgc D h0 h1 (Parts.lgc D h0 h2 h5) i r fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)).1,
    fun i r hr _ w hw x => all i r hr x w hw, fun i r hr => Parts.constituentCondition_of_hodgeJumps D h0 i r hr (all i r hr)⟩
end UpperTheory.GalS
end
end
