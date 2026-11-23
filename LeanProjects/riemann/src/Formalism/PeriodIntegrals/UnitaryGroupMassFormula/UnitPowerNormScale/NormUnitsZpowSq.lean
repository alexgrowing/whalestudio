import Mathlib
import Formalism.PeriodIntegrals.GTScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

noncomputable section

namespace PI.GTS

open Formalism.BasicNotions MvPolynomial

private theorem fockF_eq_sum_lemma {σ : Type*} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem fockF_smul_self {σ : Type*} (c : ℂ) (f : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) (c • f) = (c * star c) * Formalism.REAL.fockF f f := by
  rw [fockF_eq_sum_lemma (c • f) _ f.support MvPolynomial.support_smul,
    fockF_eq_sum_lemma f f f.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem re_normFock_smul {N : ℕ} (lam : DomWeight N) (c : ℂ) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam (c • x) (c • x)).re = ‖c‖ ^ 2 * (normFock lam x x).re := by
  unfold normFock
  rw [fockF_smul_self, mul_div_assoc]
  have hc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = (starRingEnd ℂ) c from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hc, Complex.re_ofReal_mul]

theorem norm_units_zpow_sq (u : ℂˣ) (e : ℤ) :
    ‖((u ^ e : ℂˣ) : ℂ)‖ ^ 2 = ‖(u : ℂ)‖ ^ (2 * e) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem sqAct_mem_delSq (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ delSq ℂ N lam) : sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  unfold sqAct delSq at *
  refine Submodule.smul_mem _ _ ?_
  exact Formalism.UG.P.wlocal_main le_rfl lam.natW N 0 (zero_add N) ((g : Matrix (Fin N) (Fin N) ℂ).transpose)
    ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose
    (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one])
    (fun i j hj => absurd hj (Nat.not_lt_zero _)) f hf

theorem gTScale : PI.GTScale := by
  intro n N h lam sg io br hio hbr a
  obtain ⟨-, -, -, -, hio5, hio6⟩ := hio
  obtain ⟨-, -, -, -, hbr5, hbr6⟩ := hbr
  have ha : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr a.ne_zero
  have hnn : 0 ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) := zpow_nonneg (norm_nonneg _) _
  constructor
  · intro s hs
    have hk : ‖((a⁻¹ ^ degZ lam sg : ℂˣ) : ℂ)‖ ^ 2 = ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) := by
      rw [norm_units_zpow_sq, Units.val_inv_eq_inv_val, norm_inv, inv_zpow']
    rw [hio5 a⁻¹ s hs, re_normFock_smul, hk, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hio6 s hs) hnn
  · intro f hf
    have hf' := sqAct_mem_delSq N lam (lastGL ℂ N a) f hf
    have h1 := hbr6 _ hf'
    rw [hbr5 a f hf, re_normFock_smul, norm_units_zpow_sq] at h1
    calc (normFock sg (br f) (br f)).re
        = ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * (‖(a : ℂ)‖ ^ (2 * degZ lam sg) * (normFock sg (br f) (br f)).re) := by
          rw [← mul_assoc, ← zpow_add₀ ha]; simp
      _ ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * (brBd h lam sg ^ 2 *
            (normFock lam (sqAct ℂ N lam (lastGL ℂ N a) f) (sqAct ℂ N lam (lastGL ℂ N a) f)).re) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = _ := by ring

end PI.GTS
