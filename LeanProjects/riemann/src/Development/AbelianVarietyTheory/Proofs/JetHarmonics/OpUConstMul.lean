import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.HeisOps

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem hf_add_left (x y z : Fin g → ℂ) : hf Hm (x + y) z = hf Hm x z + hf Hm y z := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin g → ℂ) : hf Hm x (y + z) = hf Hm x y + hf Hm x z := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_zero_right (x : Fin g → ℂ) : hf Hm x 0 = 0 := by simp [hf]

theorem hf_swap (h : Hm.IsHermitian) (x y : Fin g → ℂ) : hf Hm y x = conj (hf Hm x y) := by
  simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : conj (Hm i j) = Hm j i := h.apply j i
  rw [e]; ring

theorem opU_opU (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z =>
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z := by
  funext z
  simp only [opU]
  rw [add_assoc z x y, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hf_add_left, hf_add_right]
  have e := Complex.sub_conj (hf Hm x y)
  rw [hf_swap h x y]
  push_cast at e
  linear_combination (-(Real.pi : ℂ) / 2) * e

theorem opU_comm (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z => kap Hm x y * opU Hm y (opU Hm x F) z := by
  funext z
  rw [opU_opU h x y, opU_opU h y x, add_comm y x, kap, ← mul_assoc, ← Complex.exp_add, hf_swap h x y,
    Complex.conj_im]
  push_cast
  ring_nf

theorem im_eq {d : ℕ} (hd : 0 < d) (x y : Fin g → ℂ) (u v : ℤ) (h : beta d Hm x y = u + v * w0 d) :
    (hf Hm x y).im = v := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have e := congrArg Complex.im h
  rw [beta, Complex.im_ofReal_mul] at e
  have e2 : ((u : ℂ) + v * w0 d).im = Real.sqrt d / 2 * v := by
    simp [w0, rtd]; ring
  rw [e2] at e
  exact mul_left_cancel₀ (div_ne_zero hs two_ne_zero) e

theorem opU_const_mul (c : ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    opU Hm x (fun w => c * F w) z = c * opU Hm x F z := by
  simp only [opU]; ring

theorem opW_opW {d : ℕ} (hd : 0 < d) (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ)
    (hb : beta d Hm x y ∈ OK d) : opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F := by
  obtain ⟨u, v, huv⟩ := hb
  have him := im_eq hd x y u v huv
  have hre : (beta d Hm x y).re = u + v / 2 := by
    rw [huv]; simp [w0, rtd]; ring
  have hq : (beta d Hm (x + y) (x + y)).re = (beta d Hm x x).re + (beta d Hm y y).re + (2 * u + v) := by
    simp only [beta, Complex.re_ofReal_mul, hf_add_left, hf_add_right, Complex.add_re] at hre ⊢
    rw [hf_swap h x y, Complex.conj_re]
    linear_combination 2 * hre
  funext z
  have e : opW d Hm x (opW d Hm y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) *
      (Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm y y).re : ℂ)) * opU Hm x (opU Hm y F) z) := by
    rw [← opU_const_mul]; rfl
  rw [e, opU_opU h, him]
  simp only [opW]
  rw [hq, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem contDiff_opU (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  refine (hF.comp (contDiff_id.add contDiff_const)).mul (ContDiff.cexp ?_)
  fun_prop

theorem contDiff_opW (d : ℕ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opW d Hm x F) :=
  contDiff_const.mul (contDiff_opU x hF)

theorem heisenberg : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), 0 < d → Hm.IsHermitian → (∀ (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), opU Hm x (opU Hm y F) = (fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z) ∧ opU Hm x (opU Hm y F) = (fun z => kap Hm x y * opU Hm y (opU Hm x F) z) ∧ (beta d Hm x y ∈ OK d → opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F)) ∧ (∀ F, opU Hm 0 F = F ∧ opW d Hm 0 F = F) ∧ (∀ (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ (opU Hm x F) ∧ ContDiff ℂ ⊤ (opW d Hm x F)) ∧ (∀ x y : Fin g → ℂ, hf Hm y x = conj (hf Hm x y)) ∧ (∀ (x y : Fin g → ℂ) (u v : ℤ), beta d Hm x y = u + v * w0 d → (hf Hm x y).im = v) ∧ ∀ x y z : Fin g → ℂ, kap Hm x (y + z) = kap Hm x y * kap Hm x z ∧ kap Hm (x + y) z = kap Hm x z * kap Hm y z := by
  intro g d Hm hd h
  refine ⟨fun x y F => ⟨opU_opU h x y F, opU_comm h x y F, opW_opW hd h x y F⟩, fun F => ?_,
    fun x F hF => ⟨contDiff_opU x hF, contDiff_opW d x hF⟩, hf_swap h, im_eq hd, fun x y z => ⟨?_, ?_⟩⟩
  · constructor <;> funext z <;> simp [opW, opU, beta, hf_zero_right]
  · simp only [kap, hf_add_right, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring
  · simp only [kap, hf_add_left, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring

end GlobalTheory.HeisOps
