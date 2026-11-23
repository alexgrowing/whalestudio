import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_isAdj : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left),
    IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  intro K _ A B c d hc f
  obtain ⟨A', P, ⟨hP, -⟩, hdim⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  obtain ⟨φ, hφ, hiso⟩ := GlobalTheory.T.exists_hom_to_dual_of_mumfordClass K A A' P hP hdim c
  obtain ⟨n, v, hn, -, -, hvφ⟩ := exists_quasiInverse_isogeny K A A' φ (hiso hc)
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      CechPic.pull (lift (a * a') t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) =
      CechPic.pull (lift a t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) +
      CechPic.pull (lift a' t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) := by
    intro Y a a' t
    simp only [lam_eq, CechPic.pull_lam, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    simp only [← lam_eq]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K B d Y _ _ t
  have hzero : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left
      (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) = 0 := by
    rw [lam_eq, CechPic.pull_lam, lift_snd, CechPic.lam_one_right]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP _ hadd hzero
  have hpow : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (m : ℕ),
      AbDual.evc hP.isLB a (b ^ m) = m • AbDual.evc hP.isLB a b := by
    intro Y a b m
    induction m with
    | zero => rw [pow_zero, zero_smul, AbDual.evc_one_right hP.isLB hP.zero a]
    | succ m ih => rw [pow_succ, GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a, ih, succ_nsmul]
  refine ⟨n, ψ ≫ v, hn, ?_⟩
  have e1 := congrArg (CechPic.pull (lift (fst A.X B.X) (snd A.X B.X ≫ (ψ ≫ v).hom)).left) hφ
  rw [lam_eq, CechPic.pull_lam, AbDual.pull_evc, lift_fst, lift_snd_assoc, lift_snd, ← lam_eq] at e1
  unfold IsAdj
  rw [e1]
  simp only [comp_hom, Category.assoc]
  rw [← comp_hom v φ, hvφ, nsmul_hom, id_hom, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, hpow, ← hψ,
    natCast_zsmul]

end GlobalTheory.AV.AbVar
