import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.MnrUpdateEqZero

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.LowA

variable {R : Type*} [CommRing R]

lemma nuNext_castSucc {m : ℕ} (ν : Fin (m + 1) → ℕ) (t : Fin m) : nuNext ν t.castSucc = ν t.succ := by
  have ht := t.isLt
  have h : (t.castSucc : Fin (m + 1)).val + 1 < m + 1 := by rw [Fin.val_castSucc]; omega
  unfold PI.OddDualWeyl.nuNext
  rw [dif_pos h]
  congr 1

lemma nuNext_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuNext ν (Fin.last m) = 0 := by
  unfold PI.OddDualWeyl.nuNext
  rw [dif_neg (by simp)]

lemma nuStar_apply {m : ℕ} (lam : Fin (m + 1) → ℤ) (t : Fin (m + 1)) :
    nuOf (lamStar lam) t = (lam 0 - lam t.rev).toNat := by
  simp only [PI.OddDualWeyl.nuOf, PI.OddDualWeyl.lamStar, Fin.rev_last]
  congr 1
  ring

lemma nu_anti {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (t : Fin m) :
    nuOf lam t.succ ≤ nuOf lam t.castSucc := by
  have h := hlam (show t.castSucc ≤ t.succ from Fin.castSucc_lt_succ.le)
  exact Int.toNat_le_toNat (by omega)

lemma expo_castSucc {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (s : Fin m) :
    nuOf (lamStar lam) s.castSucc - nuNext (nuOf (lamStar lam)) s.castSucc =
      nuOf lam s.rev.castSucc - nuNext (nuOf lam) s.rev.castSucc := by
  rw [nuNext_castSucc, nuNext_castSucc]
  simp only [nuStar_apply, Fin.rev_castSucc, Fin.rev_succ]
  simp only [PI.OddDualWeyl.nuOf]
  have h1 := hlam (Fin.zero_le s.rev.castSucc)
  have h2 := hlam (show s.rev.castSucc ≤ s.rev.succ from Fin.castSucc_lt_succ.le)
  have h3 := hlam (Fin.le_last s.rev.succ)
  omega

lemma expo_star_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf (lamStar lam) (Fin.last m) - nuNext (nuOf (lamStar lam)) (Fin.last m) = 0 := by
  rw [nuNext_last, nuStar_apply, Fin.rev_last]
  simp

lemma expo_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf lam (Fin.last m) - nuNext (nuOf lam) (Fin.last m) = 0 := by
  rw [nuNext_last]
  simp [PI.OddDualWeyl.nuOf]

lemma prod_minors {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1))) :
    ∏ s : Fin (m + 1), pMinor R σ (m + 1 - 1 - s.val) (by omega) ^
      (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = pw R σ (nuOf lam) := by
  rw [PI.OddDualWeyl.pw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, expo_star_last,
    expo_last]
  simp only [pow_zero, mul_one]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun s => ?_)
  have hr : (Fin.revPerm s : Fin m) = s.rev := rfl
  rw [hr, expo_castSucc lam hlam s]
  congr 1
  have hs := s.isLt
  exact PI.OddDualWeyl.Low.pMinor_congr σ (by simp only [Fin.val_castSucc, Fin.val_rev]; omega) _ _

lemma tele (G : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℤ) - 1 - j) * (G j - G (j + 1)) =
      n * G 0 - ∑ j ∈ Finset.range n, G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ j ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℤ) - 1 - j) * (G j - G (j + 1)) =
        ((n : ℤ) - 1 - j) * (G j - G (j + 1)) + (G j - G (j + 1)) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    push_cast
    ring

lemma sum_expo {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∑ s : Fin (m + 1), s.val * (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = expM lam := by
  have hsplit : ∑ s : Fin (m + 1), s.val * (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam) s -
      PI.OddDualWeyl.nuNext (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam)) s) =
      ∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) := by
    rw [Fin.sum_univ_castSucc, expo_star_last, mul_zero, add_zero]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun s => ?_)
    have hr : (Fin.revPerm s : Fin m) = s.rev := rfl
    rw [hr, expo_castSucc lam hlam s, nuNext_castSucc]
    congr 1
    have hs := s.isLt
    simp only [Fin.val_castSucc, Fin.val_rev]
    omega
  have hle : ∀ t : Fin m, PI.OddDualWeyl.nuOf lam t.succ ≤ PI.OddDualWeyl.nuOf lam t.castSucc :=
    nu_anti lam hlam
  have h0 : ∀ t, PI.OddDualWeyl.nuOf lam t ≤ PI.OddDualWeyl.nuOf lam 0 := fun t =>
    Int.toNat_le_toNat (by have := hlam (Fin.zero_le t); omega)
  have hlast : PI.OddDualWeyl.nuOf lam (Fin.last m) = 0 := by simp [PI.OddDualWeyl.nuOf]
  have hsum : ∑ t, PI.OddDualWeyl.nuOf lam t = ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc := by
    rw [Fin.sum_univ_castSucc, hlast, add_zero]
  have hbound : ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc ≤ m * PI.OddDualWeyl.nuOf lam 0 := by
    calc ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc ≤ ∑ _t : Fin m, PI.OddDualWeyl.nuOf lam 0 :=
          Finset.sum_le_sum fun t _ => h0 _
      _ = m * PI.OddDualWeyl.nuOf lam 0 := by simp
  let G : ℕ → ℤ := fun j => if h : j < m + 1 then (PI.OddDualWeyl.nuOf lam ⟨j, h⟩ : ℤ) else 0
  have hG : ∀ t : Fin m, G t.val = PI.OddDualWeyl.nuOf lam t.castSucc := fun t => by
    have := t.isLt
    show (if h : t.val < m + 1 then _ else _) = _
    rw [dif_pos (by omega)]
    rfl
  have hG1 : ∀ t : Fin m, G (t.val + 1) = PI.OddDualWeyl.nuOf lam t.succ := fun t => by
    have := t.isLt
    show (if h : t.val + 1 < m + 1 then _ else _) = _
    rw [dif_pos (by omega)]
    rfl
  have hG0 : G 0 = PI.OddDualWeyl.nuOf lam 0 := by simp [G]
  have key : ((∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) : ℕ) : ℤ) =
      (m : ℤ) * PI.OddDualWeyl.nuOf lam 0 - ∑ t : Fin m, (PI.OddDualWeyl.nuOf lam t.castSucc : ℤ) := by
    have e1 : ((∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) : ℕ) : ℤ) =
        ∑ j ∈ Finset.range m, ((m : ℤ) - 1 - j) * (G j - G (j + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => ((m : ℤ) - 1 - j) * (G j - G (j + 1))) m, Nat.cast_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have h1 := t.isLt
      have h2 := hle t
      have c1 : ((m - 1 - t.val : ℕ) : ℤ) = (m : ℤ) - 1 - t.val := by omega
      have c2 : ((PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ : ℕ) : ℤ) =
          (PI.OddDualWeyl.nuOf lam t.castSucc : ℤ) - PI.OddDualWeyl.nuOf lam t.succ := by omega
      rw [Nat.cast_mul, c1, c2, hG, hG1]
    rw [e1, tele, ← Fin.sum_univ_eq_sum_range G m, hG0]
    simp only [hG]
  rw [hsplit, PI.OddDualWeyl.expM, hsum, ← Nat.cast_inj (R := ℤ), key, Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_sum]

lemma pm_prod {ι : Type*} (s : Finset ι) (u : ι → R) (e : ι → ℕ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∏ i ∈ s, u i ^ e i = 1 ∨ ∏ i ∈ s, u i ^ e i = -1 := by
  classical
  have hpow : ∀ i, u i ^ e i = 1 ∨ u i ^ e i = -1 := fun i => by
    rcases hu i with h | h
    · left
      rw [h, one_pow]
    · rw [h]
      exact neg_one_pow_eq_or R (e i)
  have hmul : ∀ a b : R, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (a * b = 1 ∨ a * b = -1) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.induction_on s ?_ ?_
  · left
    exact Finset.prod_empty
  · intro a t ha ih
    rw [Finset.prod_insert ha]
    exact hmul _ _ (hpow a) ih

lemma dualSub_C {k : ℕ} (r : R) : dualSub R k (C r) = C r := by
  simpa [MvPolynomial.algebraMap_eq] using (PI.OddDualWeyl.dualSub R k).commutes r

lemma prodStar {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1)))
    (D : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (u : Fin (m + 1) → R)
    (hu : ∀ s, u s = 1 ∨ u s = -1)
    (hD : ∀ s : Fin (m + 1), D s = C (u s) * (genM R (m + 1)).det ^ s.val *
      pMinor R σ (m + 1 - 1 - s.val) (by omega)) :
    ∃ U : R, (U = 1 ∨ U = -1) ∧
      ∏ s, D s ^ (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) =
        C U * (genM R (m + 1)).det ^ expM lam * pw R σ (nuOf lam) := by
  refine ⟨∏ s, u s ^ (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam) s - PI.OddDualWeyl.nuNext (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam)) s),
    pm_prod _ _ _ hu, ?_⟩
  simp_rw [hD, mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, sum_expo lam hlam, prod_minors lam hlam σ]
  simp only [map_prod, map_pow]

end PI.OddDualWeyl.LowA

namespace PI.OddDualWeyl

theorem highestWeightDual_of (h : JacRev) : W4hw := by
  intro R _ m lam hlam
  have hJ := fun s : Fin (m + 1) => h R (m + 1) s.val s.isLt
  choose u hu hD using hJ
  obtain ⟨U, hU, hprod⟩ := PI.OddDualWeyl.LowA.prodStar (R := R) lam hlam 1
    (fun s => dualSub R (m + 1) (pMinor R Fin.revPerm (s.val + 1) s.isLt)) u hu hD
  refine ⟨U, hU, ?_⟩
  have hC : C U * C U = (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) := by
    rw [← map_mul]
    rcases hU with rfl | rfl <;> simp
  unfold Rel low pw
  rw [map_mul, PI.OddDualWeyl.LowA.dualSub_C, map_prod]
  simp_rw [map_pow]
  rw [hprod, PI.OddDualWeyl.Low.pw_one, ← mul_assoc, ← mul_assoc, hC, one_mul]

end PI.OddDualWeyl
