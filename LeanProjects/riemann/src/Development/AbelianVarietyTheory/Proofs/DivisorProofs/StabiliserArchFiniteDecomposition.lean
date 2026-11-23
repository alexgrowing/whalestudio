import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblDatum.StabDec

open GlobalTheory.ThK.ConeEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mul_one_sub_eInf {u : AF F} (hu : sndA F u = 0) : u * (1 - eInf F) = 0 := by
  have h1 : (eInf F).1 = 1 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_one]; exact evI_realAd_one)
  refine Prod.ext ?_ ?_
  · change u.1 * (1 - (eInf F).1) = 0
    rw [h1, sub_self, mul_zero]
  · change u.2 * (1 - (eInf F).2) = 0
    rw [show u.2 = 0 from hu, zero_mul]

theorem mat_inv_compArch_mul {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    mat ((compArch σ J k)⁻¹ * k) - 1 = (1 - eInf F) • (mat k - 1) := by
  have e : mat ((compArch σ J k)⁻¹ * k) = mat (compArch σ J k⁻¹) * mat k := by rw [map_inv]; rfl
  have e' : mat k⁻¹ * mat k = 1 := by
    change mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  rw [e, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, e', smul_sub, sub_smul,
    sub_smul, one_smul, one_smul]
  abel

theorem exists_kInf_mul_fin (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (K : Subgroup (UA σ X.J)) (hK : IsStab B K) :
    ∀ k ∈ K, ∃ a ∈ KInf σ X B.emb, ∃ f ∈ K, f ∈ UAt σ X (sndA F) ∧ k = a * f := by
  intro k hk
  have ha : compArch σ X.J k ∈ K := (StabComp.comp_mem_of_isStab F E σ B n X K hK k hk).2
  refine ⟨compArch σ X.J k, ⟨compArch_mem k, ((hK _).1 ha).1⟩, (compArch σ X.J k)⁻¹ * k,
    mul_mem (inv_mem ha) hk, fun u hu => ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [mat_inv_compArch_mul, smul_smul, mul_one_sub_eInf hu, zero_smul]

end GlobalTheory.DblDatum.StabDec

end
