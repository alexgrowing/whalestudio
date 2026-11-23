import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open PI.VolStabSW PI.OmLocU.CntFF
open scoped TensorProduct

theorem prod_fin_rev (f : ℕ → ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, f (n - (j : ℕ)) = ∏ i ∈ Finset.Icc (n - a + 1) n, f i := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show n - (a + 1) + 1 = n - a by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n - a ≤ n by omega), Finset.prod_insert (by simp), mul_comm]

theorem prod_pow_rev (q : ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) = q ^ (2 * n * a - a ^ 2) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), ← pow_add]
    congr 1
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * m * a := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * m * (a + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2, show 2 * (a + 1 + m - a) - 1 = 2 * m + 1 by omega]
    ring

theorem inert_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    ∏ j : Fin a, (q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1) =
      q ^ (2 * (n - (j : ℕ)) - 1) * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf]
    have e : q ^ (2 * (n - (j : ℕ)) - 1) * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (n - (j : ℕ) - 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub (show 1 ≤ 2 * (n - (j : ℕ)) by omega), Nat.cast_sub hj.le,
        Nat.cast_sub (show 1 ≤ n - (j : ℕ) by omega)]
      ring
    rw [mul_sub, mul_one, ← e]
    ring
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_pow_rev q n a ha,
    prod_fin_rev f n a ha]

theorem split_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    (∏ i : Fin a, (q ^ n - q ^ (i : ℕ))) * q ^ (a * (n - a)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ n - q ^ (j : ℕ) = q ^ n * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf, one_pow, one_mul]
    have e : q ^ n * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (j : ℕ) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub hj.le]
      ring
    rw [mul_sub, mul_one, e]
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_fin_rev f n a ha,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have e : n * a + a * (n - a) = 2 * n * a - a ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [show a + m - a = m by omega]
    symm; apply Nat.sub_eq_of_eq_add; ring
  rw [← e, pow_add]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T'}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T'}))

theorem clsU_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedU σ J ψ v Λ a Y) : ClsU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, fFInert2_holds k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact inert_prod (qv v) hq n a ha
  · rw [hc, fFSplit_holds k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact split_prod (qv v) hq n a ha

theorem countU_of_red (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasU σ J ψ v Λ a Y)
    (hI : IdxU σ J ψ v Λ a Y) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of σ J ψ v Λ a Y hM hI (clsU_of σ J ψ v Λ a Y hR)

end PI.OmLocU
