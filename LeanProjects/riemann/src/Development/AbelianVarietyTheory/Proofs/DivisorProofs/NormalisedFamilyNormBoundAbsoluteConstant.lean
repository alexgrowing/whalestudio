import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Formalism.LocalToGlobal.GlobalTheory.GL3.ConjugateTorsionPointExists
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaZeroMeanLogLeConstMulStatement

noncomputable section
namespace GlobalTheory.ColNorms.FamilyBound
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity GlobalTheory.ColNorms

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem genusOne_meanSquare_forms_agree (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ G = GL3Theta.normSq1 Λ G :=
  (GlobalTheory.Glob.normSq1_eq_nrm1Sq Λ G).symm

theorem conj_normSq (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ))
    {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') (M : IntermediateField ℚ ℂ) (hD : DataIn D (tor0 D cc δ) M)
    (hcoef : CoefIn D (B.eNat χ N N' L L') M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (B.eNat χ N N' L L')) =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) ^ (fF D * N * N') := by
  rw [(GlobalTheory.ConjNorm.useNorm_all D cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
    (ht _ B.t0 N N' L L' hA) M ρ hD hcoef t hT).1, genusOne_meanSquare_forms_agree]

theorem conj_indep (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) :
    ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) := by
  intro N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t, hT⟩ := GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  rw [conj_normSq B χ hc ht a₁ M hD c₁ ρ hT, conj_normSq B χ hc ht a₂ M hD c₂ ρ hT]

theorem mean_le_of {C : ℝ} (hC : GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ)
    (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) : ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) := by
  intro Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t := fun ρ => GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  choose t hT using hex
  have hm := hC cc δ M t ⟨hc.1, hc.2, hD, hT⟩ Lsc hL
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t := by
    unfold meanLogNormSq GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.conjNormSq
    simp_rw [fun ρ => conj_normSq B χ hc ht hA M hD hcoef ρ (hT ρ), Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl
  rw [key]
  calc ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t
      ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

theorem familyNorms_of (hT : FamilyTie) (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) : FamilyNorms := by
  obtain ⟨C, -, hC⟩ := hM
  refine ⟨C, fun D cc δ B χ h1 h2 hcc hδ hχ hY => ?_⟩
  have ht := hT D cc δ B χ h1 h2 hcc hδ hχ hY
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h14 := theta_link_holds D cc hcc δ hδ B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ
  exact ⟨h14.1, mean_le_of (hC D) B χ hc ht, conj_indep B χ hc ht, h14.2⟩

theorem familyNorms : FamilyNorms := familyNorms_of GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul

end GlobalTheory.ColNorms.FamilyBound
