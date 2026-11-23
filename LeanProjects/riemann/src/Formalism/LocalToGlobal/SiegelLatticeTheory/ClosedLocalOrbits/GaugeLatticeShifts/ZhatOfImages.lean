import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JUMeasurableEmbedding

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

section Cons

variable {n r : ℕ} (ε : Fin n → Bool)

def lamOf (sc : ℝ) (c : Fin (r + 1) → ℂ) (b : Fin r) : ℂ :=
  c (Fin.castSucc b) / (((sc : ℂ) ^ (r - b.1))⁻¹ * ((sc : ℂ) ^ (r - b.1))⁻¹)

def alOf (T : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := -c (Fin.last r) / T

def beOf (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := ((Real.sqrt (‖c (Fin.last r)‖ ^ 2 / T - T') : ℝ) : ℂ)

theorem zhat_of_images (e f : Fin r → Fin n → ℂ) (z z' w : Fin n → ℂ) (T sc : ℝ) (β : ℂ)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzf : ∀ b, hJ ε z (f b) = 0) (hew : ∀ a, hJ ε (e a) w = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : hJ ε z w = 0) (hT : T ≠ 0) (hsc : 0 < sc) (c : Fin (r + 1) → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (hMe : ∀ b, M *ᵥ e b = lamOf sc c b • f b) (hMz : M *ᵥ z' = alOf T c • z + β • w) :
    Zhat ε (famSc sc e z) (famSc sc e z') M = Matrix.diagonal c := by
  have hsc0 : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hne : ∀ b : Fin r, Fin.last r ≠ Fin.castSucc b := fun b h => Fin.castSucc_ne_last b h.symm
  ext a b
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul, hMz,
      hJ_add_r, hJ_smul_r, hzz, hzw, mul_zero, add_zero, Matrix.diagonal_apply_eq, alOf]
    field_simp
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, mulVec_smul, hMe, hJ_smul_r, hzf, mul_zero, Matrix.diagonal_apply_ne _ (hne b)]
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, hMz, hJ_smul_l, hJ_add_r, hJ_smul_r, hez, hew, mul_zero, add_zero,
      Matrix.diagonal_apply_ne _ (hne a).symm]
  · simp only [Zhat, famSc, fam, Fin.snoc_castSucc, Fin.val_castSucc, mulVec_smul, hMe, hJ_smul_l, hJ_smul_r, hef,
      Matrix.diagonal_apply, Fin.castSucc_inj, lamOf]
    split_ifs with h
    · subst h
      simp only [map_inv₀, map_pow, Complex.conj_ofReal]
      field_simp
    · simp

theorem step_isIsom (a b : Fin n → ℂ) (hab : hJ ε a a = hJ ε b b) :
    IsIsom ε (tv ε (a - b) (hJ ε (a - b) a)⁻¹) := by
  apply tv_isIsom
  set w := hJ ε (a - b) a with hw
  have haa : conj (hJ ε a a) = hJ ε a a := hJ_self_conj ε a
  have huu : hJ ε (a - b) (a - b) = w + conj w := by
    simp only [hw, hJ_sub_left, hJ_sub_right, map_sub, haa, ← hJ_conj ε a b]
    rw [← hab]
    ring
  rw [huu]
  by_cases h0 : w = 0
  · simp [h0]
  · have h1 : conj w ≠ 0 := (map_ne_zero _).2 h0
    rw [map_inv₀]
    field_simp
    ring

theorem step_apply (a b : Fin n → ℂ) (h0 : hJ ε (a - b) a ≠ 0) : tv ε (a - b) (hJ ε (a - b) a)⁻¹ *ᵥ a = b := by
  rw [tv_apply, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem entry_eq (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : A i j = (A *ᵥ Pi.single j 1) i := by
  simp [mulVec, dotProduct, Pi.single_apply]

variable {α : Type*} [MeasurableSpace α]

theorem meas_hJ (x y : α → Fin n → ℂ) (hx : ∀ l, Measurable fun c => x c l) (hy : ∀ l, Measurable fun c => y c l) :
    Measurable fun c => hJ ε (x c) (y c) := by
  unfold hJ
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  refine (Complex.continuous_conj.measurable.comp (hx l)).mul ?_
  exact Finset.measurable_sum _ fun m _ => measurable_const.mul (hy m)

theorem meas_mul (A B : α → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, Measurable fun c => A c i j)
    (hB : ∀ i j, Measurable fun c => B c i j) : ∀ i j, Measurable fun c => (A c * B c) i j := fun i j => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

theorem meas_tvm {ι : Type} [Fintype ι] [DecidableEq ι] (u : α → ι → Fin n → ℂ) (ξ : α → ι → ℂ)
    (hu : ∀ b l, Measurable fun c => u c b l) (hξ : ∀ b, Measurable fun c => ξ c b) :
    ∀ i j, Measurable fun c => tvm ε (u c) (ξ c) i j := fun i j => by
  simp only [entry_eq _ i j, tvm_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine measurable_const.sub (Finset.measurable_sum _ fun b _ => ?_)
  exact ((hξ b).mul (meas_hJ ε (fun c => u c b) (fun _ => Pi.single j 1) (hu b) fun _ => measurable_const)).mul
    (hu b i)

theorem meas_tv (u : α → Fin n → ℂ) (ξ : α → ℂ) (hu : ∀ l, Measurable fun c => u c l) (hξ : Measurable ξ) :
    ∀ i j, Measurable fun c => tv ε (u c) (ξ c) i j := fun i j => by
  simp only [entry_eq _ i j, tv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact measurable_const.sub ((hξ.mul (meas_hJ ε u (fun _ => Pi.single j 1) hu fun _ => measurable_const)).mul (hu i))

end Cons

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
