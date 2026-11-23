import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SeesawSumTarget

variable {D : D7}

theorem isHeckeChar_mul {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((χ * η : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => χ x * η x := by
      funext x; simp
    rw [this]
    exact hχ.1.mul hη.1
  · simp only [MonoidHom.mul_apply, hχ.2 x, hη.2 x, mul_one]

theorem exists_scalar {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, GlobalTheory.WeilUniq.om_om_inv, map_smul] at this

section Std
open GlobalTheory.MixModel

theorem qA_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qA = (fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) 0).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qA, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A)]
  · simp only [fromCols_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem qB_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qB = (fromCols (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E) 1).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qB, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp only [fromCols_apply_inr]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det B)]

theorem pA_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pA ⬝ x = topR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pA, rat, qA_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, topR]
  simp [apply_ite (incA D)]

theorem pB_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pB ⬝ x = botR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pB, rat, qB_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply, botR]
  simp [apply_ite (incA D)]

theorem boxT_sumDec (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    (GlobalTheory.BiTransfer.sumDec A B).boxT S φ φ' = box2 φ φ' := by
  funext x
  simp only [OrthDec.boxT, OrthDec.resT_apply, box2]
  rw [pA_sumDec, pB_sumDec]

theorem emb_sumDec (A B : HSp D) (g : GA D A) (g₁ : GA D B) :
    (GlobalTheory.BiTransfer.sumDec A B).emb (g, g₁) = GlobalTheory.SquareComm.blk A B (g, g₁) := by
  apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum A B)
  rw [(GlobalTheory.BiTransfer.sumDec A B).mt_emb, GlobalTheory.SquareComm.mt_blk]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.Doubling.blkMat, submatrix_apply, Equiv.symm_apply_apply, Matrix.add_apply, Matrix.mul_apply,
    OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, qA_sumDec, qB_sumDec, Matrix.map_apply, id]
  simp only [GlobalTheory.BiTransfer.sumDec, submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [Matrix.one_apply, apply_ite (incA D), ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Std

theorem seesaw_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  intro D ψ hψ S A B χ₁ χ₁' χ₂ χ₂' ω₁ ω₂ H₁ H₂
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω₂', H₂'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S B χ₁ χ₂' hη H₁.hecS H₂.hecT H₁.resS H₂.resT
  obtain ⟨ω, H⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.Doubling.hsum A B) χ₁ (χ₁' * χ₂') hη H₁.hecS
    (isHeckeChar_mul H₁.hecT H₂.hecT) H₁.resS (resEta_mul H₁.resT H₂.resT)
  choose c hc using fun p => exists_scalar H₂' H₂ p
  refine ⟨ω, χ₁, χ₁' * χ₂', fun u _ g₁ => (c (u, g₁) : ℂ), H, fun u _ g₁ => Circle.norm_coe _,
    fun φ φ' hφ hφ' => ⟨?_, fun u g g₁ => ?_⟩⟩
  · rw [← boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec A B).isThetaFunO_boxT hφ hφ'
  · have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ₁ χ₁' χ₂' ω ω₁
      ω₂' H H₁ H₂' u g g₁ φ φ' hφ hφ'
    simp only [thetaKO]
    rw [← emb_sumDec, ← boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero, hc (u, g₁) φ' hφ', Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.SeesawSumTarget
