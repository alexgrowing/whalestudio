import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.HformEntry

noncomputable section

namespace PI.VolStabSW.OrbR

open Matrix Formalism.UG PIW.AdelicOrbitU

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

def r1 (c : S) (u v : Fin n → S) : Matrix (Fin n) (Fin n) S :=
  1 - c • vecMulVec v (vecMul (fun i => s (u i)) J)

private lemma hform_eq_lemma (M : Matrix (Fin n) (Fin n) S) (u z : Fin n → S) :
    hform s M u z = (fun i => s (u i)) ⬝ᵥ (M *ᵥ z) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem reflection_mulVec (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  unfold r1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  ext k
  simp only [hform, Matrix.mulVec, dotProduct, vecMulVec, vecMul, Matrix.smul_apply,
    Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec (T : Matrix (Fin n) (Fin n) S) (z w : Fin n → S) :
    hform s J (T *ᵥ z) (T *ᵥ w) = hform s (cT s T * J * T) z w := by
  rw [hform_eq_lemma, hform_eq_lemma]
  have e : (fun i => s ((T *ᵥ z) i)) = (T.map s) *ᵥ (fun i => s (z i)) := by
    funext i
    exact RingHom.map_mulVec s T z i
  rw [e]
  unfold cT
  calc (T.map s *ᵥ fun i => s (z i)) ⬝ᵥ (J *ᵥ (T *ᵥ w))
      = ((J *ᵥ (T *ᵥ w)) ᵥ* (T.map s)) ⬝ᵥ (fun i => s (z i)) := by
        rw [dotProduct_comm, dotProduct_mulVec]
    _ = (fun i => s (z i)) ⬝ᵥ ((T.map s)ᵀ *ᵥ (J *ᵥ (T *ᵥ w))) := by
        rw [dotProduct_comm, mulVec_transpose]
    _ = (fun i => s (z i)) ⬝ᵥ (((T.map s)ᵀ * J * T) *ᵥ w) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem hform_mem (g : GL (Fin n) S) (hg : g ∈ UJ s J) (z w : Fin n → S) :
    hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ z) ((g : Matrix (Fin n) (Fin n) S) *ᵥ w) =
      hform s J z w := by
  rw [hform_mulVec]
  have hg' : cT s (g : Matrix (Fin n) (Fin n) S) * J * (g : Matrix (Fin n) (Fin n) S) = J := hg
  rw [hg']

private lemma hform_single_single_stabilizer_orbit_volume (M : Matrix (Fin n) (Fin n) S) (a b : Fin n) :
    hform s M (Pi.single a 1) (Pi.single b 1) = M a b := by
  simp [hform, Pi.single_apply, apply_ite s]

theorem mem_UJ_of (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hM : cT s T * J * T = J := by
    ext a b
    have h := key (Pi.single a 1) (Pi.single b 1)
    rwa [hform_mulVec, hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at h
  have hdT : IsUnit T.det := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (cT s T).det = s T.det := by
      unfold cT
      rw [Matrix.det_transpose]
      exact (RingHom.map_det s T).symm
    rw [h2] at h1
    have h3 : s T.det * T.det * J.det = 1 * J.det := by linear_combination h1
    have h4 : s T.det * T.det = 1 := hdet.mul_left_inj.mp h3
    exact ⟨⟨T.det, s T.det, by rw [mul_comm]; exact h4, h4⟩, rfl⟩
  refine ⟨Matrix.nonsingInvUnit T hdT, ?_, rfl⟩
  show cT s T * J * T = J
  exact hM

theorem step (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by
  have hconj := hform_conj s J hs hJ
  obtain ⟨c, hc_def⟩ : ∃ c, hform s J a a - s lam * hform s J b a = c := ⟨_, rfl⟩
  rw [hc_def] at hc
  obtain ⟨ci, hci⟩ : ∃ ci, c * ci = 1 := hc.exists_right_inv
  have e2 : ci * c = 1 := by rw [mul_comm]; exact hci
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  obtain ⟨u, hu_def⟩ : ∃ u, a - lam • b = u := ⟨_, rfl⟩
  have hua : hform s J u a = c := by
    rw [← hu_def, hform_sub_left, hform_smul_left, hc_def]
  have huu : hform s J u u = c + s c := by
    rw [← hu_def, ← hc_def]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul,
      hs, hconj]
    linear_combination (s lam * lam) * hab + hform s J a a * hlam
  have key1 : ∀ z w, hform s J (r1 s J ci u u *ᵥ z) (r1 s J ci u u *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, huu]
    linear_combination (hform s J z u * hform s J u w * s ci) * e2 +
      (hform s J z u * hform s J u w * ci) * e3
  obtain ⟨g1, hg1U, hg1⟩ := mem_UJ_of s J hdet _ key1
  obtain ⟨βi, hβ⟩ : ∃ βi, hform s J a a * βi = 1 := hu.exists_right_inv
  have hsβ : s (hform s J a a) = hform s J a a := hconj a a
  have hsβi : s βi = βi := by
    have h1 : hform s J a a * s βi = 1 := by rw [← hsβ, ← map_mul, hβ, map_one]
    calc s βi = s βi * (hform s J a a * βi) := by rw [hβ, mul_one]
      _ = (hform s J a a * s βi) * βi := by ring
      _ = βi := by rw [h1, one_mul]
  have key2 : ∀ z w, hform s J (r1 s J ((1 - s lam) * βi) b b *ᵥ z)
      (r1 s J ((1 - s lam) * βi) b b *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, hab,
      map_sub, map_one, hs, hsβi]
    linear_combination (hform s J z b * hform s J b w * βi) * hlam +
      (hform s J z b * hform s J b w * (1 - lam) * (1 - s lam) * βi) * hβ
  obtain ⟨g2, hg2U, hg2⟩ := mem_UJ_of s J hdet _ key2
  refine ⟨g2 * g1, mul_mem hg2U hg1U, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hua, e2, one_smul, ← hu_def,
      sub_sub_cancel, reflection_mulVec, hform_smul_right, hab, ← sub_smul]
    conv_rhs => rw [← one_smul S b]
    congr 1
    linear_combination hlam + (s lam * lam - lam) * hβ
  · intro z hz1 hz2
    have hzu : hform s J u z = 0 := by
      rw [← hu_def, hform_sub_left, hform_smul_left, hz1, hz2, mul_zero, sub_zero]
    rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hzu, mul_zero, zero_smul, sub_zero,
      reflection_mulVec, hz2, mul_zero, zero_smul, sub_zero]

theorem orb_orth (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by
  intro k
  induction k with
  | zero => intro x y _ _ _ _; exact ⟨1, one_mem _, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro x y ho hg hu hl
    obtain ⟨g', hg'U, hg'⟩ := ih (fun i => x i.succ) (fun i => y i.succ)
      (fun i j hij => ho _ _ (fun e => hij (Fin.succ_injective _ e))) (fun i j => hg _ _)
      (fun i => hu _) (fun i t => hl _ t)
    obtain ⟨a, ha⟩ : ∃ a, (g' : Matrix (Fin n) (Fin n) S) *ᵥ x 0 = a := ⟨_, rfl⟩
    have haa : hform s J a a = hform s J (x 0) (x 0) := by rw [← ha]; exact hform_mem s J g' hg'U _ _
    obtain ⟨lam, hlam, hc⟩ := hl 0 (hform s J (y 0) a)
    rw [← haa] at hc
    obtain ⟨g1, hg1U, hg1a, hg1z⟩ := step s J hs hJ hdet a (y 0) (by rw [haa]; exact hg 0 0)
      (haa ▸ hu 0) lam hlam hc
    refine ⟨g1 * g', mul_mem hg1U hg'U, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Units.val_mul, ← mulVec_mulVec, ha]; exact hg1a
    · have hi := hg' i
      rw [Units.val_mul, ← mulVec_mulVec, hi]
      apply hg1z
      · rw [← hi, ← ha, hform_mem s J g' hg'U]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm
      · rw [hg 0 i.succ]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm

def tM {m : ℕ} (X : Fin m → Fin n → S) : Matrix (Fin n) (Fin m) S := Matrix.of fun r i => X i r

theorem gram_tM {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by
  simp only [hform, cT, tM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {m k : ℕ} (N : Matrix (Fin n) (Fin m) S) (Q : Matrix (Fin m) (Fin k) S) :
    cT s (N * Q) * J * (N * Q) = cT s Q * (cT s N * J * N) * Q := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end PI.VolStabSW.OrbR
