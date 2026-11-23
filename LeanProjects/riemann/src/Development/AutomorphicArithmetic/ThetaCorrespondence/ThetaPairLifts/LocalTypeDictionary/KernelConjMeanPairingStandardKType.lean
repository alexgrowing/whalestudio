import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjTopAtOfRankLeOfWeightLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjugateRowBoundOfDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandardStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj
namespace GlobalTheory.KerConjMean
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Std
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
end Std
theorem kernel_conj_mean_pairing_standard_KType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨F1, k1⟩ := _root_.GlobalTheory.T.kernel_conjugation_average hP hI hD hDp C1 hC1
  obtain ⟨F2, k2⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  obtain ⟨F3, k3⟩ := _root_.GlobalTheory.T.conjRowAt_of_dict_depth hP hI hD hDp C1 hC1
  obtain ⟨F4, k4⟩ := GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants
  refine ⟨max (max F1 F2) (max F3 F4), fun CF hCF => ?_⟩
  obtain ⟨C01, l1⟩ := k1 CF (by simp only [max_le_iff] at hCF; exact hCF.1.1)
  obtain ⟨C02, l2⟩ := k2 CF (by simp only [max_le_iff] at hCF; exact hCF.1.2)
  obtain ⟨C03, l3⟩ := k3 CF (by simp only [max_le_iff] at hCF; exact hCF.2.1)
  obtain ⟨C04, l4⟩ := k4 CF (by simp only [max_le_iff] at hCF; exact hCF.2.2)
  refine ⟨2 * max (max C01 C02) (max C03 C04), fun ε C hC => ?_⟩
  have hC' : max (max C01 C02) (max C03 C04) ≤ C / 2 := by linarith
  simp only [max_le_iff] at hC'
  obtain ⟨x1, m1⟩ := l1 ε (C / 2) hC'.1.1
  obtain ⟨x2, m2⟩ := l2 ε (C / 2) hC'.1.2
  obtain ⟨x3, m3⟩ := l3 ε (C / 2) hC'.2.1
  obtain ⟨x4, m4⟩ := l4 ε (C / 2) hC'.2.2
  refine ⟨max (max x1 x2) (max x3 x4), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  exact pairStdAt_of ch C large₂.sc.b C1 hmA hmT
    (fun σ => GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ)
    (m2 D large₂ hε hx.1.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m1 D large₂ hε hx.1.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m4 D large₂ hε hx.2.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m3 D large₂ hε hx.2.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end GlobalTheory.KerConjMean
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mean_kernel_pairing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  first | exact @_root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | exact _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | (intros; apply _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType <;> assumption)
end
