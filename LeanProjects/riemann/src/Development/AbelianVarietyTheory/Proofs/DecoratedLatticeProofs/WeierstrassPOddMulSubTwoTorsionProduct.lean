import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.OddHalfProduct

open Formalism.L2.Th1.F

def qf (L : PeriodPair) (y ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * herm L y ω + (Real.pi : ℂ) * herm L ω ω / 2)

lemma sg_quasi (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (y : ℂ) :
    sgStar L (y + ω) = qf L y ω * sgStar L y := by
  rw [sgStarQuasi L ω y hω]; rfl

lemma qf_ne (L : PeriodPair) (y ω : ℂ) : qf L y ω ≠ 0 := by
  unfold qf semiChar
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  split_ifs <;> norm_num

lemma qf_shift (L : PeriodPair) (y z ω : ℂ) :
    qf L (y + z) ω = qf L y ω * Complex.exp ((Real.pi : ℂ) * herm L z ω) := by
  unfold qf
  have : (Real.pi : ℂ) * herm L (y + z) ω + (Real.pi : ℂ) * herm L ω ω / 2
      = ((Real.pi : ℂ) * herm L y ω + (Real.pi : ℂ) * herm L ω ω / 2) + (Real.pi : ℂ) * herm L z ω := by
    unfold herm; ring
  rw [this, Complex.exp_add]; ring

lemma sg_ne (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : sgStar L z ≠ 0 :=
  fun h => hz (((sgStarBasic L).2.2.1 z).1 h)

lemma sg_zero (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) : sgStar L z = 0 :=
  ((sgStarBasic L).2.2.1 z).2 hz

lemma sg_neg (L : PeriodPair) (z : ℂ) : sgStar L (-z) = -sgStar L z := (sgStarBasic L).2.1 z

lemma iso_prod (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (hn : (n : ℂ) ≠ 0) (hst : MulStable L n)
    (hS : IsKerReps L n S) (hev : Even S.card) (w : ℂ) :
    (∏ P ∈ S, sgStar L P ^ 2) * sgStar L (n * w) ^ 2
      = (n : ℂ) ^ 2 * (sgStar L w ^ 2 * ∏ P ∈ S, (sgStar L (w + P) * sgStar L (w - P))) := by
  by_cases hw : w ∈ L.lattice
  · rw [sg_zero L (hst w hw), sg_zero L hw]; ring
  · have hI := isogenySigma L n S hn hst hS w hw
    have h2 : ∏ P ∈ S, (sgStar L (w + P) * sgStar L (w - P))
        = ∏ P ∈ S, ((-1) * (sgStar L w ^ 2 * sgStar L P ^ 2 * (L.weierstrassP w - L.weierstrassP P))) :=
      Finset.prod_congr rfl (fun P hP => by rw [sgStarAdd L w P hw (hS.1 P hP).2]; ring)
    rw [h2]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow]
    rw [hI]; ring

lemma sigma_id (L : PeriodPair) (n m : ℕ) (hnC : (n : ℂ) = 2 * m + 1) (S : Finset ℂ) (t : ℂ)
    (hn : (n : ℂ) ≠ 0) (hst : MulStable L n) (hS : IsKerReps L n S) (hev : Even S.card)
    (hcard : (S.card : ℂ) + 1 = (n : ℂ) ^ 2)
    (ht : t ∉ L.lattice) (h2t : 2 * t ∈ L.lattice) (z : ℂ) :
    (∏ P ∈ S, sgStar L (t + P) ^ 2) * (sgStar L (n * z + t) * sgStar L (n * z - t))
      = sgStar L (z + t) * sgStar L (z - t)
        * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P)) := by
  have h2mt : (m : ℂ) * (2 * t) ∈ L.lattice := by rw [← nsmul_eq_mul]; exact nsmul_mem h2t m
  let Φ₁ : ℂ → ℂ := fun z => qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t)
  let Φ₂ : ℂ → ℂ := fun z => qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t)
  let G : ℂ → ℂ := fun z => sgStar L (z + t) * sgStar L (z - t)
    * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))
  let F : ℂ → ℂ := fun z => sgStar L (n * z + t) * sgStar L (n * z - t)
  let D : ℂ := ∏ P ∈ S, sgStar L (t + P) ^ 2
  let C : ℂ := ∏ P ∈ S, sgStar L P ^ 2
  have hG : ∀ z, sgStar L (z + t) ^ 2 * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z + t - P))
      = Φ₁ z * G z := by
    intro z
    have e1 : sgStar L (z + t) = qf L (z - t) (2 * t) * sgStar L (z - t) := by
      rw [← sg_quasi L h2t]; congr 1; ring
    have e2 : ∀ P, sgStar L (z + t + P) * sgStar L (z + t - P)
        = qf L (z - t - P) (2 * t) * (sgStar L (z + t + P) * sgStar L (z - t - P)) := by
      intro P; rw [show z + t - P = (z - t - P) + 2 * t by ring, sg_quasi L h2t]; ring
    rw [Finset.prod_congr rfl (fun P _ => e2 P), Finset.prod_mul_distrib]
    show _ = (qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t))
      * (sgStar L (z + t) * sgStar L (z - t) * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P)))
    linear_combination (sgStar L (z + t) * (∏ P ∈ S, qf L (z - t - P) (2 * t))
      * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))) * e1
  have hF : ∀ z, sgStar L (n * (z + t)) ^ 2 = Φ₂ z * F z := by
    intro z
    have e1 : sgStar L (n * (z + t)) = qf L (n * z + t) (m * (2 * t)) * sgStar L (n * z + t) := by
      rw [← sg_quasi L h2mt]; congr 1; rw [hnC]; ring
    have e2 : sgStar L (n * z + t) = qf L (n * z - t) (2 * t) * sgStar L (n * z - t) := by
      rw [← sg_quasi L h2t]; congr 1; ring
    rw [e1]
    show _ = (qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t))
      * (sgStar L (n * z + t) * sgStar L (n * z - t))
    linear_combination (qf L (n * z + t) (m * (2 * t)) ^ 2 * sgStar L (n * z + t)) * e2
  have hΦ : ∀ z, Φ₁ z * Φ₂ 0 = Φ₁ 0 * Φ₂ z := by
    intro z
    have a0 : qf L (z - t) (2 * t) = qf L (0 - t) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) := by
      rw [show z - t = (0 - t) + z by ring, qf_shift]
    have a1 : ∀ P, qf L (z - t - P) (2 * t)
        = qf L (0 - t - P) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) := by
      intro P; rw [show z - t - P = (0 - t - P) + z by ring, qf_shift]
    have b0 : qf L (n * z + t) (m * (2 * t))
        = qf L (n * 0 + t) (m * (2 * t)) * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (m * (2 * t))) := by
      rw [show (n : ℂ) * z + t = (n * 0 + t) + n * z by ring, qf_shift]
    have b1 : qf L (n * z - t) (2 * t)
        = qf L (n * 0 - t) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (2 * t)) := by
      rw [show (n : ℂ) * z - t = (n * 0 - t) + n * z by ring, qf_shift]
    have hE : Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) ^ (S.card + 1)
        = Complex.exp ((Real.pi : ℂ) * herm L (n * z) (m * (2 * t))) ^ 2
          * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (2 * t)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      rw [hcard, hnC]
      simp only [herm, map_mul, map_natCast, map_ofNat]
      ring
    show (qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t)) * Φ₂ 0
      = Φ₁ 0 * (qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t))
    rw [a0, Finset.prod_congr rfl (fun P _ => a1 P), Finset.prod_mul_distrib, Finset.prod_const, b0, b1]
    show _ = (qf L (0 - t) (2 * t) * ∏ P ∈ S, qf L (0 - t - P) (2 * t))
      * ((qf L (n * 0 + t) (m * (2 * t)) * _) ^ 2 * (qf L (n * 0 - t) (2 * t) * _))
    rw [show ∀ a b c d e : ℂ, a * e * (b * e ^ S.card) * (c ^ 2 * d) = a * b * (c ^ 2 * d) * e ^ (S.card + 1)
      from fun a b c d e => by ring, hE]
    ring
  have star : ∀ z, (n : ℂ) ^ 2 * Φ₁ z * G z = C * Φ₂ z * F z := by
    intro z
    have h1 := iso_prod L n S hn hst hS hev (z + t)
    have h2 := hG z
    have h3 := hF z
    linear_combination (-1 : ℂ) * h1 - (n : ℂ) ^ 2 * h2 + C * h3
  have k1 : ∀ z, (n : ℂ) ^ 2 * Φ₁ 0 * G z = C * Φ₂ 0 * F z := by
    intro z
    have hne : Φ₂ z ≠ 0 := mul_ne_zero (pow_ne_zero 2 (qf_ne _ _ _)) (qf_ne _ _ _)
    apply mul_right_cancel₀ hne
    linear_combination Φ₂ 0 * star z - (n : ℂ) ^ 2 * G z * hΦ z
  have hF0 : F 0 = -sgStar L t ^ 2 := by
    show sgStar L (n * 0 + t) * sgStar L (n * 0 - t) = _
    rw [mul_zero, zero_add, zero_sub, sg_neg]; ring
  have hF0ne : F 0 ≠ 0 := by rw [hF0]; exact neg_ne_zero.mpr (pow_ne_zero 2 (sg_ne L ht))
  have hG0 : G 0 = D * F 0 := by
    have e : ∀ P, sgStar L (0 + t + P) * sgStar L (0 - t - P) = (-1) * sgStar L (t + P) ^ 2 := by
      intro P; rw [zero_add, show (0 : ℂ) - t - P = -(t + P) by ring, sg_neg]; ring
    rw [hF0]
    show sgStar L (0 + t) * sgStar L (0 - t) * ∏ P ∈ S, (sgStar L (0 + t + P) * sgStar L (0 - t - P)) = _
    rw [Finset.prod_congr rfl (fun P _ => e P), Finset.prod_mul_distrib, Finset.prod_const,
      hev.neg_one_pow, zero_add, zero_sub, sg_neg]
    ring
  have hC : C * Φ₂ 0 = (n : ℂ) ^ 2 * Φ₁ 0 * D := by
    apply mul_right_cancel₀ hF0ne
    have := k1 0
    rw [hG0] at this
    linear_combination -this
  have hne : (n : ℂ) ^ 2 * Φ₁ 0 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hn)
      (mul_ne_zero (qf_ne _ _ _) (Finset.prod_ne_zero_iff.mpr (fun P _ => qf_ne _ _ _)))
  show D * F z = G z
  apply mul_left_cancel₀ hne
  linear_combination -(k1 z) - F z * hC

theorem wp_odd_mul_sub_half_prod : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n →
    Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice →
    (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P)
      = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  intro L n S t hodd hS ht h2t z hnz
  obtain ⟨m, hm⟩ := hodd
  have hnC : (n : ℂ) = 2 * m + 1 := by rw [hm]; push_cast; ring
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hst : MulStable L n := fun ω hω => by rw [← nsmul_eq_mul]; exact nsmul_mem hω n
  have hcardR := kerRepsCard L n S hn hst hS
  have hcardN : S.card + 1 = n ^ 2 := by
    have : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by rw [Complex.normSq_apply]; simp; ring
    rw [this] at hcardR; exact_mod_cast hcardR
  have hcard : (S.card : ℂ) + 1 = (n : ℂ) ^ 2 := by exact_mod_cast hcardN
  have hS4 : S.card = 4 * (m * m + m) :=
    Nat.add_right_cancel (by rw [hcardN, hm]; ring : S.card + 1 = 4 * (m * m + m) + 1)
  have hev : Even S.card := ⟨2 * (m * m + m), by rw [hS4]; ring⟩
  have hzL : z ∉ L.lattice := fun h => hnz (by rw [← nsmul_eq_mul]; exact nsmul_mem h n)
  have htP : ∀ P ∈ S, t + P ∉ L.lattice := by
    intro P hP h
    have hnP := (hS.1 P hP).1
    have h2P : 2 * P ∈ L.lattice := by
      have := sub_mem (nsmul_mem h 2) h2t
      convert this using 1; rw [nsmul_eq_mul]; push_cast; ring
    have hPL : P ∈ L.lattice := by
      have := sub_mem hnP (nsmul_mem h2P m)
      convert this using 1; rw [nsmul_eq_mul, hnC]; ring
    exact (hS.1 P hP).2 hPL
  have hsig := sigma_id L n m hnC S t hn hst hS hev hcard ht h2t z
  have hD : ∏ P ∈ S, sgStar L (t + P) ^ 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun P hP => pow_ne_zero 2 (sg_ne L (htP P hP)))
  have hM : sgStar L z ^ (2 * (S.card + 1)) * sgStar L t ^ 2 * ∏ P ∈ S, sgStar L (t + P) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sg_ne L hzL)) (pow_ne_zero 2 (sg_ne L ht))) hD
  apply mul_right_cancel₀ hM
  have hI := isogenySigma L n S hn hst hS z hzL
  have hadd1 := sgStarAdd L (n * z) t hnz ht
  have hadd2 := sgStarAdd L z t hzL ht
  have hprod : ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))
      = (sgStar L z ^ 2) ^ S.card * (∏ P ∈ S, sgStar L (t + P) ^ 2)
        * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
    have e : ∀ P ∈ S, sgStar L (z + t + P) * sgStar L (z - t - P)
        = (-1) * (sgStar L z ^ 2 * sgStar L (t + P) ^ 2 * (L.weierstrassP z - L.weierstrassP (t + P))) := by
      intro P hP
      rw [show z + t + P = z + (t + P) by ring, show z - t - P = z - (t + P) by ring,
        sgStarAdd L z (t + P) hzL (htP P hP)]
      ring
    rw [Finset.prod_congr rfl e]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow]
    ring
  linear_combination (-((L.weierstrassP (n * z) - L.weierstrassP t) * sgStar L t ^ 2
      * ∏ P ∈ S, sgStar L (t + P) ^ 2)) * hI
    + (∏ P ∈ S, sgStar L (t + P) ^ 2) * hadd1 - hsig
    - (∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))) * hadd2
    + (sgStar L z ^ 2 * sgStar L t ^ 2 * (L.weierstrassP z - L.weierstrassP t)) * hprod

end GlobalTheory.OddHalfProduct
