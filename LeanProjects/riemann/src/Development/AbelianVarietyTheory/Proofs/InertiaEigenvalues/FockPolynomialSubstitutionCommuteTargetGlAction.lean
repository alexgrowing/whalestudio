import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

noncomputable section
open MvPolynomial

namespace GlobalTheory.FockSubstComm

variable {D : D7} {m n : ℕ}

def rowMat (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if (i : ℕ) < p τ then ((g τ)⁻¹).val else ((g τ).val)ᵀ

theorem fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (v : FVar D m n) :
    fockSubst p g (X v) = ∑ b, C (rowMat p g v.1 v.2.1 v.2.2 b) * X (v.1, v.2.1, b) := by
  rw [fockSubst, aeval_X, rowMat]
  split_ifs <;> simp

open Classical in
theorem pderiv_fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (b : Fin n)
    (u : FVar D m n) :
    pderiv (τ, i, b) (fockSubst p g (X u)) = if u.1 = τ ∧ u.2.1 = i then C (rowMat p g τ i u.2.2 b) else 0 := by
  rw [fockSubst_X]
  simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X, smul_eq_mul]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [Finset.sum_eq_single b]
    · simp [Pi.single_apply]
    · intro c _ hc; simp [Pi.single_apply, Prod.ext_iff, hc]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : (u.1, u.2.1, c) ≠ (τ, i, b) := by
      intro e; simp [Prod.ext_iff] at e; exact h ⟨e.1, e.2.1⟩
    simp [Pi.single_apply, this]

theorem chain_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (u : FVar D m n) :
    fockSubst p g (pderiv (τ, i, c) (X u)) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g (X u)) := by
  classical
  simp only [pderiv_fockSubst_X]
  rw [pderiv_X]
  by_cases h : u.1 = τ ∧ u.2.1 = i
  · simp only [if_pos h]
    have e : (∑ b, C' b c • C (rowMat p g τ i u.2.2 b) : PolF D m n) = C ((rowMat p g τ i * C') u.2.2 c) := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_C_mul, ← map_mul, mul_comm]
    rw [e, hC]
    obtain ⟨u1, u2, u3⟩ := u
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1; subst h2
    by_cases h3 : u3 = c
    · subst h3; simp
    · have : ((u1, u2, u3) : FVar D m n) ≠ (u1, u2, c) := by simp [h3]
      simp [Pi.single_apply, this, Matrix.one_apply, h3]
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]
    have : u ≠ (τ, i, c) := by
      rintro rfl; exact h ⟨rfl, rfl⟩
    simp [Pi.single_apply, this]

theorem chain (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (P : PolF D m n) :
    fockSubst p g (pderiv (τ, i, c) P) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P u ih =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib]
    rw [ih, chain_X p g τ i c C' hC u, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_smul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem rai_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i c =
      ∑ b, ((g τ)⁻¹).val c b • (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (i : ℕ) < p τ
  · simp only [raiO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]
  · have hC : rowMat p g τ i * (((g τ)⁻¹).val)ᵀ = 1 := by
      rw [rowMat, if_neg h, ← Matrix.transpose_mul]
      simp
    simp only [raiO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.neg_apply, map_neg, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Derivation.coeFn_coe, Bool.false_eq_true, if_false]
    rw [chain p g τ i c _ hC, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem low_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (l : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l c =
      ∑ b, (g τ).val b c • (lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (l : ℕ) < p τ
  · have hC : rowMat p g τ l * (g τ).val = 1 := by
      rw [rowMat, if_pos h]
      simp
    simp only [lowO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
    rw [chain p g τ l c _ hC]
  · simp only [lowO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Bool.false_eq_true, if_false]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in
theorem pair_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i l : Fin m) :
    Commute (fockSubst p g).toLinearMap
      (∑ j, raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i j *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l j) := by
  set σ := (fockSubst p g).toLinearMap
  set R := raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i
  set L := lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l
  have hR : ∀ c, σ * R c = ∑ b, ((g τ)⁻¹).val c b • (R b * σ) := rai_comm p g τ i
  have hL : ∀ c, σ * L c = ∑ b, (g τ).val b c • (L b * σ) := low_comm p g τ l
  have hGG : ∀ c b, ∑ j, (g τ).val c j * ((g τ)⁻¹).val j b = (1 : Matrix (Fin n) (Fin n) ℂ) c b := by
    intro c b
    rw [← Matrix.mul_apply]
    simp
  unfold Commute SemiconjBy
  calc σ * ∑ j, R j * L j
      = ∑ j, ∑ b, ∑ c, (((g τ)⁻¹).val j b * (g τ).val c j) • (R b * L c * σ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, hR, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_mul_assoc, mul_assoc, hL, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_smul_comm, smul_smul, ← mul_assoc]
    _ = ∑ b, ∑ c, (∑ j, (g τ).val c j * ((g τ)⁻¹).val j b) • (R b * L c * σ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = (∑ j, R j * L j) * σ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators in

theorem fockSubst_fockT (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n) :
    fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) =
      fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  have hc : Commute (fockSubst p g).toLinearMap
      (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y) := by
    unfold fockT
    refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun l _ => Commute.smul_right ?_ _
    rw [Finset.sum_add_distrib]
    refine Commute.add_right (pair_comm p g τ i l) (Commute.sum_right _ _ _ fun j _ => ?_)
    split_ifs
    · exact Commute.smul_right (Commute.one_right _) _
    · exact Commute.zero_right _
  have := LinearMap.congr_fun hc.eq P
  simpa only [Module.End.mul_apply, AlgHom.toLinearMap_apply] using this

end GlobalTheory.FockSubstComm
