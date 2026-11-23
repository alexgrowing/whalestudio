import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbSuccMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTwo
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.FlagTwoDom

open Matrix GlobalTheory.ThK.FlagSemi GlobalTheory.LeviUnitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ n₂ : ℕ}

theorem incM_ιTwo_mulVec (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (z : Fin n₂ → AE F E) :
    incM F (ιTwo H₁ H₂) *ᵥ z = incM F H₁.ι *ᵥ (incM F H₂.ι *ᵥ z) := by
  rw [ιTwo, incM_mul, mulVec_mulVec]

theorem levi_conj_mem {Y : Spc F E n} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {H : Plane E n n₁}
    {π : Matrix (Fin n₁) (Fin n) E} (hF : IsFrame σ Y.J J₁ H π) (m : UA σ Y.J) (hm : m ∈ unip σ Y H) (h : UA σ J₁) :
    hF.1.levi h * m * (hF.1.levi h)⁻¹ ∈ unip σ Y H := by
  rw [GlobalTheory.UnipCT.unip_eq] at hm ⊢
  obtain ⟨hm1, hm2⟩ := hm
  have hfix : ∀ g : UA σ J₁, mat (hF.1.levi g) *ᵥ incV F H.x = incV F H.x := fun g => hF.1.levi_fix g hF.πx
  rw [← map_inv]
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hfix, hm1, hfix]
  · obtain ⟨a, ha⟩ := hm2 (mat h⁻¹ *ᵥ z)
    refine ⟨a, ?_⟩
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hF.1.levi_ι, ha, mulVec_add, mulVec_smul, hfix,
      hF.1.levi_ι, Matrix.mulVec_mulVec z (mat h) (mat h⁻¹), mat_mul_inv, one_mulVec]

theorem proj_unip {Y : Spc F E n} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {H : Plane E n n₁}
    {π : Matrix (Fin n₁) (Fin n) E} (hF : IsFrame σ Y.J J₁ H π) {m : UA σ Y.J} (hm : m ∈ unip σ Y H)
    (y : Fin n₁ → AE F E) (c : AE F E) :
    incM F π *ᵥ (mat m *ᵥ (incM F H.ι *ᵥ y + c • incV F H.x)) = y := by
  rw [GlobalTheory.UnipCT.unip_eq] at hm
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨a, ha⟩ := hm2 y
  rw [mulVec_add, mulVec_smul, hm1, ha, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hF.πx, hF.1.π_ι]
  simp

end GlobalTheory.ThK.DescB.FlagTwoDom

end
