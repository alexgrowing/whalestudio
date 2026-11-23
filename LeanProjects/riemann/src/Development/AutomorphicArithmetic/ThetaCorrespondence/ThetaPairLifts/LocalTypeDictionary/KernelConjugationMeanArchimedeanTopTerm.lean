import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjTopAtOfRankLeOfWeightLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepthStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
namespace GlobalTheory.KerConjMean
theorem archimedean_top_term_kernel_conj_mean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨CF0, hCF⟩ := _root_.GlobalTheory.T.kernel_conjugation_average hP hI hD hDp C1 hC1
  obtain ⟨CF0', hCF'⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  refine ⟨max CF0 CF0', fun CF hCF0 => ?_⟩
  obtain ⟨C0, hC0⟩ := hCF CF (le_trans (le_max_left _ _) hCF0)
  obtain ⟨C0', hC0'⟩ := hCF' CF (le_trans (le_max_right _ _) hCF0)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC0 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x0', hx0'⟩ := hC0' ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  obtain ⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩ :=
    hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  have hrat := hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  refine ⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · refine (meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)
    have e1 := mul_le_mul_of_nonneg_left hmA hnD
    have e2 := mul_le_mul_of_nonneg_left hmT hGd
    nlinarith
  · intro p Φ β d hocc c j B v hv
    obtain ⟨f, hf⟩ := hrat Φ β d hocc c j
    obtain ⟨u, rfl, hu⟩ := hv
    refine ⟨f u, (hf u).symm, ?_⟩
    obtain ⟨hfin, hne⟩ := GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding
    obtain ⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩ := exists_avg _ hfin hne a0 nD Gd
      (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)
    rcases le_or_gt 0 B with hB | hB
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans
        (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)
end GlobalTheory.KerConjMean
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_conjugation_mean_archimedean_top_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  first | exact @_root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean | exact _root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean | (intros; apply _root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean <;> assumption)
end
