import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.HformEntry

noncomputable section

namespace PI.VolStabS.OrbR

open Matrix Formalism.UG PIW.AdelicOrbitU

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

def r1 (c : S) (u v : Fin n → S) : Matrix (Fin n) (Fin n) S :=
  1 - c • vecMulVec v (vecMul (fun i => s (u i)) J)

theorem reflection_mulVec (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  have hf : hform s J u z = (fun i => s (u i)) ⬝ᵥ (J *ᵥ z) := by
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [r1, Matrix.sub_mulVec, Matrix.one_mulVec, hf, Matrix.dotProduct_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hform_mulVec (T : Matrix (Fin n) (Fin n) S) (z w : Fin n → S) :
    hform s J (T *ᵥ z) (T *ᵥ w) = hform s (cT s T * J * T) z w := by
  have hf : ∀ (M : Matrix (Fin n) (Fin n) S) (x y : Fin n → S),
      hform s M x y = (fun i => s (x i)) ⬝ᵥ (M *ᵥ y) := by
    intro M x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => s ((T *ᵥ z) i)) = (T.map s) *ᵥ (fun i => s (z i)) :=
    funext fun i => RingHom.map_mulVec s T z i
  rw [hf, hf, hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp only [cT, Matrix.mul_assoc]

theorem hform_mem (g : GL (Fin n) S) (hg : g ∈ UJ s J) (z w : Fin n → S) :
    hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ z) ((g : Matrix (Fin n) (Fin n) S) *ᵥ w) =
      hform s J z w := by
  rw [hform_mulVec]
  rw [show cT s (g : Matrix (Fin n) (Fin n) S) * J * (g : Matrix (Fin n) (Fin n) S) = J from hg]

theorem mem_UJ_of (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hsingle : ∀ (M : Matrix (Fin n) (Fin n) S) (i j : Fin n),
      hform s M (Pi.single i 1) (Pi.single j 1) = M i j := by
    intro M i j
    simp [hform, Pi.single_apply, apply_ite s]
  have hM : cT s T * J * T = J := by
    ext i j
    have h1 := key (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hsingle, hsingle] at h1
  have h2 := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : (cT s T).det * T.det = 1 :=
    hdet.mul_left_cancel (by linear_combination h2)
  have hT : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (IsUnit.of_mul_eq_one_right _ h3)
  refine ⟨hT.unit, ?_, hT.unit_spec⟩
  show cT s (hT.unit : Matrix (Fin n) (Fin n) S) * J * (hT.unit : Matrix (Fin n) (Fin n) S) = J
  rw [hT.unit_spec]
  exact hM

theorem step (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by
  have hJ' : ∀ i j, s (J i j) = J j i := by
    intro i j
    have h1 := congrFun (congrFun hJ j) i
    simpa [cT] using h1
  have hsub1 : ∀ x y z : Fin n → S, hform s J (x - y) z = hform s J x z - hform s J y z := by
    intro x y z
    simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  have hsub2 : ∀ x y z : Fin n → S, hform s J x (y - z) = hform s J x y - hform s J x z := by
    intro x y z
    simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hsmul1 : ∀ (c : S) (x z : Fin n → S), hform s J (c • x) z = s c * hform s J x z := by
    intro c x z
    simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsmul2 : ∀ (c : S) (x z : Fin n → S), hform s J x (c • z) = c * hform s J x z := by
    intro c x z
    simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hherm : ∀ x y : Fin n → S, hform s J y x = s (hform s J x y) := by
    intro x y
    simp only [hform, map_sum, map_mul, hs, hJ']
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hRu : ∀ (k : S) (w : Fin n → S), k + s k = s k * k * hform s J w w →
      ∀ z y, hform s J (r1 s J k w w *ᵥ z) (r1 s J k w w *ᵥ y) = hform s J z y := by
    intro k w hk z y
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hsub1, hsub2, hsmul1, hsmul2, map_mul]
    rw [hherm w z]
    linear_combination (-(hform s J w y * s (hform s J w z))) * hk
  have hq : s (hform s J a a) = hform s J a a := (hherm a a).symm
  have hba : hform s J a b = s (hform s J b a) := hherm b a
  have hwa : hform s J (a - lam • b) a = hform s J a a - s lam * hform s J b a := by
    rw [hsub1, hsmul1]
  have e1 : s (hform s J a a - s lam * hform s J b a) = hform s J a a - lam * s (hform s J b a) := by
    rw [map_sub, map_mul, hs, hq]
  have hww : hform s J (a - lam • b) (a - lam • b) =
      (hform s J a a - s lam * hform s J b a) + s (hform s J a a - s lam * hform s J b a) := by
    simp only [hsub1, hsub2, hsmul1, hsmul2]
    linear_combination (-lam) * hba + (s lam * lam) * hab + hform s J a a * hlam - e1
  obtain ⟨ci, hci⟩ : ∃ ci : S, ci * (hform s J a a - s lam * hform s J b a) = 1 := ⟨_, hc.val_inv_mul⟩
  have hci' : s ci * s (hform s J a a - s lam * hform s J b a) = 1 := by
    rw [← map_mul, hci, map_one]
  have hk1 : ci + s ci =
      s ci * ci * hform s J (a - lam • b) (a - lam • b) := by
    linear_combination (-s ci) * hci + (-ci) * hci' +
      (-(s ci * ci)) * hww
  obtain ⟨qi, hqi⟩ : ∃ qi : S, qi * hform s J a a = 1 := ⟨_, hu.val_inv_mul⟩
  have hsqi : s qi = qi := by
    have h1 : s qi * hform s J a a = 1 := by
      have h2 := congrArg s hqi
      rwa [map_mul, hq, map_one] at h2
    calc s qi = s qi * (hform s J a a * qi) := by
          rw [mul_comm (hform s J a a), hqi, mul_one]
      _ = qi := by rw [← mul_assoc, h1, one_mul]
  have hk2 : (1 - s lam) * qi + s ((1 - s lam) * qi) =
      s ((1 - s lam) * qi) * ((1 - s lam) * qi) * hform s J b b := by
    simp only [map_mul, map_sub, map_one, hs, hsqi]
    linear_combination (-qi) * hlam -
      (1 - lam - s lam + lam * s lam) * qi ^ 2 * hab -
      (1 - lam - s lam + lam * s lam) * qi * hqi
  have hM : ∀ z y, hform s J ((r1 s J ((1 - s lam) * qi) b b *
      r1 s J ci (a - lam • b) (a - lam • b)) *ᵥ z)
      ((r1 s J ((1 - s lam) * qi) b b *
      r1 s J ci (a - lam • b) (a - lam • b)) *ᵥ y) = hform s J z y := by
    intro z y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hRu _ _ hk2, hRu _ _ hk1]
  obtain ⟨g, hg, hgM⟩ := mem_UJ_of s J hdet _ hM
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hgM, ← Matrix.mulVec_mulVec, reflection_mulVec s J ci (a - lam • b) (a - lam • b) a, hwa, hci, one_smul, sub_sub_cancel, reflection_mulVec, hsmul2,
      ← sub_smul]
    convert one_smul S b using 2
    linear_combination hlam - (1 - s lam) * lam * qi * hab - (1 - s lam) * lam * hqi
  · intro z hz1 hz2
    rw [hgM, ← Matrix.mulVec_mulVec, reflection_mulVec s J ci (a - lam • b) (a - lam • b) z, hsub1, hsmul1, hz1, hz2]
    simp only [mul_zero, sub_zero, zero_smul]
    rw [reflection_mulVec, hz2]
    simp

theorem orb_orth (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by
  intro k
  induction k with
  | zero =>
    intro x y _ _ _ _
    exact ⟨1, one_mem _, fun i => i.elim0⟩
  | succ k ih =>
    intro x y horth hgram hunit hlam
    obtain ⟨g, hg, hgx⟩ := ih (fun i => x i.castSucc) (fun i => y i.castSucc)
      (fun i j hij => horth _ _ (fun h => hij (Fin.castSucc_injective _ h))) (fun i j => hgram _ _)
      (fun i => hunit _) (fun i t => hlam _ t)
    have hpres := hform_mem s J g hg
    have hab : hform s J (y (Fin.last k)) (y (Fin.last k)) =
        hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) := by
      rw [hpres, hgram]
    have hu : IsUnit (hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))
        ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))) := by
      rw [hpres]
      exact hunit _
    obtain ⟨lam, hl1, hl2⟩ := hlam (Fin.last k)
      (hform s J (y (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)))
    have hc : IsUnit (hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))
        ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k)) - s lam *
        hform s J (y (Fin.last k)) ((g : Matrix (Fin n) (Fin n) S) *ᵥ x (Fin.last k))) := by
      rw [hpres]
      exact hl2
    obtain ⟨g', hg', hg'a, hg'fix⟩ := step s J hs hJ hdet _ _ hab hu lam hl1 hc
    refine ⟨g' * g, mul_mem hg' hg, fun i => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    induction i using Fin.lastCases with
    | last => exact hg'a
    | cast j =>
      have hj := hgx j
      rw [hj]
      apply hg'fix
      · rw [← hj, hpres]
        exact horth _ _ (Fin.castSucc_lt_last j).ne'
      · rw [hgram]
        exact horth _ _ (Fin.castSucc_lt_last j).ne'

def tM {m : ℕ} (X : Fin m → Fin n → S) : Matrix (Fin n) (Fin m) S := Matrix.of fun r i => X i r

theorem gram_tM {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by
  simp only [hform, cT, tM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {m k : ℕ} (N : Matrix (Fin n) (Fin m) S) (Q : Matrix (Fin m) (Fin k) S) :
    cT s (N * Q) * J * (N * Q) = cT s Q * (cT s N * J * N) * Q := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

end PI.VolStabS.OrbR
