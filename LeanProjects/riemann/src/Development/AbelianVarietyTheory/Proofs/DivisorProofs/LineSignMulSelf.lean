import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.CCRSig

variable {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

def unitAtS (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

theorem sum_unitAtS [Fintype W] (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAtS j z w a b * star (unitAtS k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w0, a0, b0⟩ := j
  obtain ⟨w1, a1, b1⟩ := k
  rw [Finset.sum_eq_single w0]
  · by_cases hw : w1 = w0
    · subst hw
      simp only [unitAtS, Pi.single_eq_same]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · by_cases ha : a0 = a1
        · subst ha
          by_cases hb : b0 = b1
          · subst hb; simp
          · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a0, b1⟩ := by
              intro h; simp at h; exact hb h
            simp [this, hb, Ne.symm hb]
        · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
            intro h; simp at h; exact ha h.1
          simp [this, ha, Ne.symm ha]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    · have : (⟨w0, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
        intro h; exact hw (congrArg Sigma.fst h).symm
      simp [unitAtS, hw, this]
  · intro w _ hw; simp [unitAtS, hw]
  · simp

theorem sum_unitAtS_eq [Fintype W] (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), unitAtS j (c j.1 j.2.1 j.2.2) := by
  funext w a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Fintype.sum_sigma, unitAtS]
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Matrix.single_apply, hb]
    · simp
    · intro a' _ ha; simp [Matrix.single_apply, ha]
    · simp
  · intro w' _ hw; simp [Pi.single_eq_of_ne' hw]
  · simp

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD.CCRSig

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [← mul_inv]
  congr 1
  linear_combination 4 * h

def ccrM (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))

def ccrD (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I)))

theorem ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : ccrM H j * ccrM H k = ccrM H k * ccrM H j := by
  have h11 := hc (unitAtS j 1) (unitAtS k 1)
  have h1i := hc (unitAtS j 1) (unitAtS k Complex.I)
  have hi1 := hc (unitAtS j Complex.I) (unitAtS k 1)
  have hii := hc (unitAtS j Complex.I) (unitAtS k Complex.I)
  rw [sum_unitAtS] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold ccrM
    have c : Commute (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))
        (H (unitAtS k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAtS k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

theorem ccrD_ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) :
    ccrD H j * ccrM H k - ccrM H k * ccrD H j = if j = k then 1 else 0 := by
  unfold ccrD ccrM
  rw [comm_expand, hc, hc, hc, hc, sum_unitAtS, sum_unitAtS, sum_unitAtS, sum_unitAtS,
    inv_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : j = k
  · subst h
    simp only [if_true, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    conv_rhs => rw [← one_smul ℂ (1 : Module.End ℂ V)]
    congr 1
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
  · simp [h]

theorem unitAtS_re_im (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) :
    unitAtS j z = ((z.re : ℝ) : ℂ) • unitAtS j 1 + ((z.im : ℝ) : ℂ) • unitAtS j Complex.I := by
  funext w
  by_cases hw : w = j.1
  · subst hw
    simp only [unitAtS, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul,
      mul_one, Complex.re_add_im]
  · simp [unitAtS, Pi.single_eq_of_ne hw]

theorem heis_expanccrD [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hadd : ∀ c c', H (c + c') = H c + H c') (hsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c)
    (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrD H j) := by
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), H (unitAtS j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAtS_eq c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAtS_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold ccrM ccrD GlobalTheory.CCRFock.coefM GlobalTheory.CCRFock.coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAtS j 1) = A
  generalize H (unitAtS j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD

open GlobalTheory.HoweD.CCRSig in

theorem ccr_fock_ops_sig : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ} (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V), (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) → (∀ c c', H c * H c' - H c' * H c = ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) → ∃ m D : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) → Module.End ℂ V, (∀ i j, m i * m j = m j * m i) ∧ (∀ i j, D i * m j - m j * D i = if i = j then 1 else 0) ∧ (∀ (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (f₀ : V), H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 1)) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 Complex.I)) f₀ = 0 → D j f₀ = 0) ∧ ∀ c, H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • m j + (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • D j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hc
  refine ⟨ccrM H, ccrD H, ccrM_comm H hc, ccrD_ccrM_comm H hc, fun j f₀ h => ?_, heis_expanccrD H hadd hsmul⟩
  have h' : H (unitAtS j 1) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I) f₀ = 0 := h
  simp only [GlobalTheory.HoweD.CCRSig.ccrD, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, h', smul_zero, neg_zero]

end GlobalTheory.HoweD
