import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
open GlobalTheory.SplitDblGen

namespace GlobalTheory.SplitDblGen

theorem inlD_mem_closure_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp _ h2 k hk
  obtain ⟨c, hcσ, hcAt, hc2, hcL⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hTr.base v hsp
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ _ G.W v h2 c hcσ hcAt (hcL _ G.W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ _ G.W v h2 c hcσ (hcL _ G.W) k hk
  have hg := GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer F E σ _ G.W v k hk
  have hKK' : mat k * mat k⁻¹ = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (mul_inv_cancel k)
  have hK'K : mat k⁻¹ * mat k = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (inv_mul_cancel k)
  have hAtK : At (evFin F v) (mat k - 1) := hk.1
  have hAtK' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [Matrix.mul_sub, hK'K, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hAtK u hu, Matrix.mul_zero, neg_zero]
  have hc2M : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), At (evFin F v) M → (c * c) • M = M := by
    intro M hM
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc2 _ (fun u hu => by
      have h0 := congrFun (congrFun (hM u hu) i) j
      simpa using h0)
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k) (mat k⁻¹) hKK' (hc2M _ hAtK)
  have ht' := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k⁻¹) (mat k) hK'K (hc2M _ hAtK')
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E _ c (mat k) (mat k⁻¹) hKK' hK'K (hc2M _ hAtK)
  let T : GL (Fin (a + a')) (AE F E) := ⟨tMat c (mat k), tMat c (mat k⁻¹), ht, ht'⟩
  have hinv : GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD n = 1 := GlobalTheory.DblVacFlip.matD_inv_mul n
  have hq : n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k ∈ GlobalTheory.InertDbl.ParD σ G.W v := by
    refine ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.inv_mem_KD hn.1) hp.1) hg, T, ?_⟩
    show GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD p * GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ G.W k) *
        diagCols (Fin (a + a')) = diagCols (Fin (a + a')) * tMat c (mat k)
    have h3 := congrArg (fun M => GlobalTheory.InertDbl.matD n⁻¹ * M) hid
    simp only [← Matrix.mul_assoc] at h3
    rw [GlobalTheory.InertDbl.matD_inlD, hpm]
    refine h3.trans ?_
    rw [← hnm, hinv]
    exact congrArg (· * tMat c (mat k)) (Matrix.one_mul _)
  have e : GlobalTheory.InertDbl.inlD σ G.W k = p⁻¹ * n * (n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k) := by group
  rw [e]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (s _ (Or.inl hp))) (s _ (Or.inr hn))) (s _ (Or.inl hq))

end GlobalTheory.SplitDblGen

end
