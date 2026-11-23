import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGenLeft

open GlobalTheory.InertDbl GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_smul_eq {n : Type} {v : Pl F} {c : AE F E} (hc : ∀ z : AE F E, At (evFin F v) z → c * c * z = z)
    {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : (c * c) • X = X := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hc _ fun u hu => by simpa using congrFun (congrFun (hX u hu) i) j

theorem inlD_mem_closure_of_split {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl F)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) :
    inlD σ W k ∈ Subgroup.closure (ParD σ W v ∪ NabD σ W v) := by
  obtain ⟨c, hcσ, hcat, hcsq, hclat⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hv
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ d W v h2 c hcσ hcat (hclat d W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ d W v h2 c hcσ (hclat d W) k hk
  have e1 : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e2 : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hsq : (c * c) • (mat k - 1) = mat k - 1 := sq_smul_eq hcsq hk.1
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E d c (mat k) (mat k⁻¹) e1 e2 hsq
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E d c (mat k) (mat k⁻¹) e1 hsq
  let t : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, mul_eq_one_comm.1 ht⟩
  have hq : n⁻¹ * (p * inlD σ W k) ∈ ParD σ W v := by
    refine ⟨KAtD_mul (KAtD_inv hn.1) (KAtD_mul hp.1 (inlD_mem hk)), t, ?_⟩
    have en : matD n⁻¹ * matD n = 1 := (n.1).inv_val
    show matD n⁻¹ * (matD p * matD (inlD σ W k)) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    rw [matD_inlD, hpm]
    rw [← hnm] at hid
    erw [Matrix.mul_assoc, hid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, en, Matrix.one_mul]
    rfl
  have e : inlD σ W k = p⁻¹ * (n * (n⁻¹ * (p * inlD σ W k))) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl hp)))
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hn)) (Subgroup.subset_closure (Or.inl hq)))

theorem inlD_mem_closure_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv _ h2 k hk
  exact inlD_mem_closure_of_split hT.base G.V' v hv h2 k hk

end GlobalTheory.SplitDblGenLeft
end
