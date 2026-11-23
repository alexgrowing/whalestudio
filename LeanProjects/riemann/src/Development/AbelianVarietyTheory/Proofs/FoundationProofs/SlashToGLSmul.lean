import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

noncomputable section

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wOld (N l : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), a; (N : ℤ) * l, (l : ℤ) * b]

def gaOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (j : ℤ) + a; (N : ℤ), (N : ℤ) * j + l * b], by
    rw [Matrix.det_fin_two_of]; linear_combination h⟩

def trOld (k : ℤ) (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ) : ℍ → ℂ :=
  G + ∑ j ∈ Finset.range l, G ∣[k] gaOld N l a b h j

def ChiInv (k : ℤ) (N M : ℕ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → G ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • G

def CuspAll (k : ℤ) (G : ℍ → ℂ) : Prop :=
  MDiff G ∧ ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt G k

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL
  rw [dif_neg hg]
  rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g).det : ℝ) = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_val g hg, ← RingHom.map_det]
  simp

lemma toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  apply Units.ext
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh]
  exact map_mul (Int.castRingHom ℝ).mapMatrix g h

lemma slash_SL_eq (k : ℤ) (γ : SL(2, ℤ)) (G : ℍ → ℂ) : G ∣[k] γ = G ∣[k] toGL (mat γ) := by
  rw [ModularForm.SL_slash]
  congr 1
  apply Units.ext
  rw [toGL_val _ (by simp [mat])]
  ext i j
  simp [mat]

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma sigma_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℂ) : σ g z = z := by
  rw [σ, if_pos hg]
  rfl

lemma slash_scalar (k : ℤ) (c : ℝ) (hc : 0 < c) (G : ℍ → ℂ) :
    G ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')) = ((c : ℂ) ^ (k - 2)) • G := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val = c ^ 2 := by
    simp [Matrix.GeneralLinearGroup.det_scalar]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val := by
    rw [hdet]; positivity
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ModularForm.slash_apply, sigma_pos hpos, hdet, abs_of_pos (by positivity),
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  have he : (c : ℂ) ^ (k - 2) = (c : ℂ) ^ (((2 : ℕ) : ℤ) * (k - 1)) * (c : ℂ) ^ (-k) := by
    rw [← zpow_add₀ hc']
    congr 1
    push_cast
    ring
  rw [he]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g hg.ne']
  exact_mod_cast hg

lemma smul_slash_toGL (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (c : ℂ) (G : ℍ → ℂ) :
    (c • G) ∣[k] toGL M = c • (G ∣[k] toGL M) := by
  rw [ModularForm.smul_slash, sigma_pos (toGL_det_pos M hM)]

lemma toGL_smul (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    toGL ((c : ℤ) • g) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c : ℝ) (by positivity)) * toGL g := by
  have h1 : ((c : ℤ) • g).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hg, hc.ne']
  apply Units.ext
  rw [Units.val_mul, toGL_val _ h1, toGL_val _ hg, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul,
    Units.val_mk0, Matrix.smul_apply, smul_eq_mul]
  simp

lemma slash_toGL_smul (k : ℤ) (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det)
    (G : ℍ → ℂ) : G ∣[k] toGL ((c : ℤ) • g) = ((c : ℂ) ^ (k - 2)) • (G ∣[k] toGL g) := by
  rw [toGL_smul c hc g hg.ne', SlashAction.slash_mul, slash_scalar k (c : ℝ) (by positivity),
    smul_slash_toGL k g hg, Complex.ofReal_natCast]

lemma ulFam_det (l : ℕ) (hl : 0 < l) (j : Fin l) : 0 < (ulFam l j).det := by
  simp [ulFam, Matrix.det_fin_two_of]
  exact_mod_cast hl

lemma ulF_add (k : ℤ) (l : ℕ) (F G : ℍ → ℂ) : UlF k l (F + G) = UlF k l F + UlF k l G := by
  simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]

lemma ulF_smul (k : ℤ) (l : ℕ) (hl : 0 < l) (c : ℂ) (F : ℍ → ℂ) : UlF k l (c • F) = c • UlF k l F := by
  simp only [UlF, hkF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_slash_toGL k _ (ulFam_det l hl j) c F

lemma ulF_sub (k : ℤ) (l : ℕ) (hl : 0 < l) (F G : ℍ → ℂ) : UlF k l (F - G) = UlF k l F - UlF k l G := by
  have h := ulF_smul k l hl (-1) G
  rw [sub_eq_add_neg, ulF_add, sub_eq_add_neg]
  congr 1
  simpa using h

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices
open CongruenceSubgroup

lemma chiInv_add {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F G : ℍ → ℂ} (hF : ChiInv k N M χ F)
    (hG : ChiInv k N M χ G) : ChiInv k N M χ (F + G) := by
  intro γ hγ
  rw [SlashAction.add_slash, hF γ hγ, hG γ hγ, smul_add]

lemma chiInv_smul {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} (c : ℂ) (hF : ChiInv k N M χ F) :
    ChiInv k N M χ (c • F) := by
  intro γ hγ
  rw [ModularForm.SL_smul_slash, hF γ hγ, smul_comm]

lemma cuspAll_add {k : ℤ} {F G : ℍ → ℂ} (hF : CuspAll k F) (hG : CuspAll k G) : CuspAll k (F + G) := ⟨hF.1.add hG.1, fun c hc => (hF.2 c hc).add (hG.2 c hc)⟩

lemma cuspAll_smul {k : ℤ} {F : ℍ → ℂ} (c : ℂ) (hF : CuspAll k F) : CuspAll k (c • F) := by
  refine ⟨hF.1.const_smul c, fun p hp g hg => ?_⟩
  rw [ModularForm.smul_slash]
  exact Filter.ZeroAtFilter.smul _ (hF.2 p hp g hg)

end GlobalTheory.HeckeFamilyMatrices
