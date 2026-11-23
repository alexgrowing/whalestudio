import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmJumpSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.HostJumpWin
open Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
open Classical in
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  intro _ D L P nch HW F Cm X C₂ S ep hJa
  obtain ⟨-, hJb, hJc, -⟩ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (S.facts.admJ L S.par)
  intro i _ w hw C τ
  obtain ⟨g, ρ, hR, hjx, -⟩ := hJa i (X.r i) (S.canon.fam.good i) w hw C τ
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  obtain ⟨hlo, hhi⟩ := sz_bounds L P S.par (D.nd.j i) hj1 hj2 ρ
  have hUp : EmbeddingTypeJumps.UpAt ep C τ → AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ =>
    typeU_of_emb i C τ g ρ hR ep τ₀ h0 e0
  have hDn : EmbeddingTypeJumps.DownAt ep C τ → ¬ AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ h => by
    have h' := typeU_of_emb i C τ g ρ hR (!ep) τ₀ h0 e0
    unfold AdmissibleParameterJ.TypeU at h h'
    cases ep <;> simp_all
  obtain ⟨s, Jc, Jl, h1, h2, h3, h4, h5, hpos, hneg, hJJ⟩ :=
    key_sets L hJb hJc (D.nd.j i) hj1 hj2 ρ (decide (AdmissibleParameterJ.TypeU D ep g)) hlo hhi
  refine ⟨s, Jc, Jl, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_⟩
  · by_cases ht : AdmissibleParameterJ.TypeU D ep g
    · left; exact hpos (by simp [ht])
    · right; exact hneg (by simp [ht])
  · intro hu; exact hpos (by simp [hUp hu])
  · intro hd; exact hneg (by simp [hDn hd])
  · intro x a
    exact ((hjx x a).1).trans (hJJ a)
end GlobalTheory.HostJumpWin
end
end
