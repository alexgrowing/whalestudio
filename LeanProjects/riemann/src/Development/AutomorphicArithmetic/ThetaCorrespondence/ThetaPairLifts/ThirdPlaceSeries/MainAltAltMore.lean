import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.HubFon
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  intro hF D _L hG hJa r ρ hP i hi w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hi.1.1
  have h0 : D.nd.l i ≠ D.host.g 0 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 0).1 h.symm
    · exact (g_ne_q_d D 0).2 h.symm
  have h1 : D.nd.l i ≠ D.host.g 1 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 1).1 h.symm
    · exact (g_ne_q_d D 1).2 h.symm
  obtain ⟨π₀, hπ₀⟩ := hi.2
  have hg0 : π₀ ∈ D.nd.Zgood i := (D.Zgood_tie i π₀).2 hπ₀
  have hZ0 := LargeLevelLemmas.zgoodSubsetZ i hg0
  have hd0 : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (r i) (ρ i) π₀ := by
    obtain ⟨e, he⟩ := (hP.compl i π₀ hZ0).rho
    exact ⟨e, fun g u => he g u⟩
  have hc := (_root_.GlobalTheory.CrysFromGTwo.main_alt_alt hF D i (r i) (ρ i) π₀ (hP.good i) (hG i _ (hP.good i)) h0 h1 hd0 w hw C).2
  have K := GlobalTheory.TateDualCrys.crystalline_and_jumps D i w hw (D.locT (D.nd.l i)) C.LL C.le (r i) (ρ i)
    (fun x => (hc x).2)
  refine ⟨fun V1 _ _ _ _ _ ρ1 hs => K.1 V1 ρ1 hs, fun π hπ => ?_⟩
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r i π) (ρ i π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := (hP.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  refine K.2 π hdec (fun τ a => ?_)
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i (r i) (hP.good i) w hw C τ
  have := (hx π a).2.1
  rw [this]
  split_ifs <;> norm_num
end GlobalTheory.HubFon
end
