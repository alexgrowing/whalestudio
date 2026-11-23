import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def LineDeg {r : ℕ} (i : Fin r) (d : ℕ) (g : (Fin r → ℕ) → ℂ) : Prop :=
  ∀ m : Fin r → ℕ, ∃ q : Polynomial ℂ, q.degree < (d : WithBot ℕ) ∧
    ∀ t : ℕ, g (m + t • (Pi.single i 1 : Fin r → ℕ)) = q.eval (t : ℂ)

theorem degree_shift_sub_lt (q : Polynomial ℂ) (d : ℕ) (hq : q.degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    (q.comp (Polynomial.X + 1) - q).degree < (d : WithBot ℕ) := by
  by_cases h0 : q.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    simp
  · have hq0 : q ≠ 0 := fun h => h0 (by simp [h])
    have hX : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X_add_C 1
    have hnat : (q.comp (Polynomial.X + 1)).natDegree = q.natDegree := by
      rw [Polynomial.natDegree_comp, hX, mul_one]
    have hlc : (q.comp (Polynomial.X + 1)).leadingCoeff = q.leadingCoeff := by
      have hm : (Polynomial.X + 1 : Polynomial ℂ).Monic := Polynomial.monic_X_add_C 1
      rw [Polynomial.leadingCoeff_comp (by rw [hX]; exact one_ne_zero), hm.leadingCoeff, one_pow, mul_one]
    have hp0 : q.comp (Polynomial.X + 1) ≠ 0 := by
      intro h
      apply hq0
      rw [← Polynomial.leadingCoeff_eq_zero, ← hlc, h, Polynomial.leadingCoeff_zero]
    have hdeg : (q.comp (Polynomial.X + 1)).degree = q.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, hnat]
    have hlt := Polynomial.degree_sub_lt hdeg hp0 hlc
    rw [hdeg, Polynomial.degree_eq_natDegree hq0] at hlt
    rw [Polynomial.degree_eq_natDegree hq0] at hq
    have h1 : q.natDegree < d + 1 := by exact_mod_cast hq
    have h2 : q.natDegree ≤ d := Nat.lt_succ_iff.mp h1
    exact lt_of_lt_of_le hlt (by exact_mod_cast h2)

theorem LineDeg.fd_self {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i (d + 1) g) : LineDeg i d (fd i g) := by
  intro m
  obtain ⟨q, hq, hg⟩ := h m
  refine ⟨q.comp (Polynomial.X + 1) - q, degree_shift_sub_lt q d hq, fun t => ?_⟩
  have e1 : m + t • (Pi.single i 1 : Fin r → ℕ) + Pi.single i 1 =
      m + (t + 1) • (Pi.single i 1 : Fin r → ℕ) := by
    rw [add_smul, one_smul, add_assoc]
  simp only [fd]
  rw [e1, hg, hg, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Nat.cast_add, Nat.cast_one]

theorem LineDeg.fd_any {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (k : Fin r)
    (h : LineDeg i d g) : LineDeg i d (fd k g) := by
  intro m
  obtain ⟨q₁, hq₁, hg₁⟩ := h (m + Pi.single k 1)
  obtain ⟨q₂, hq₂, hg₂⟩ := h m
  refine ⟨q₁ - q₂, lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hq₁ hq₂), fun t => ?_⟩
  simp only [fd]
  rw [add_right_comm, hg₁, hg₂, Polynomial.eval_sub]

theorem LineDeg.eq_zero {r : ℕ} {i : Fin r} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i 0 g) (m : Fin r → ℕ) : g m = 0 := by
  obtain ⟨q, hq, hg⟩ := h m
  have hq0 : q = 0 := by
    by_contra hne
    rw [Polynomial.degree_eq_natDegree hne] at hq
    have : q.natDegree < 0 := by exact_mod_cast hq
    omega
  have := hg 0
  simp only [zero_smul, add_zero, hq0, Polynomial.eval_zero] at this
  exact this

theorem LineDeg.DL {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (h : LineDeg i d g)
    (cs : List (Fin r)) : LineDeg i (d - cs.count i) (DL cs g) := by
  induction cs with
  | nil => simpa [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL] using h
  | cons c cs ih =>
    have e : GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL (c :: cs) g = fd c (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL cs g) := rfl
    rw [e]
    by_cases hc : c = i
    · rw [hc, List.count_cons_self]
      rcases Nat.eq_zero_or_pos (d - cs.count i) with h0 | hpos
      · have h3 : d - (cs.count i + 1) = 0 := by omega
        rw [h3]
        rw [h0] at ih
        exact ih.fd_any i
      · obtain ⟨e', he⟩ : ∃ e', d - cs.count i = e' + 1 := ⟨d - cs.count i - 1, by omega⟩
        have h3 : d - (cs.count i + 1) = e' := by omega
        rw [h3]
        rw [he] at ih
        exact ih.fd_self
    · have h3 : (c :: cs).count i = cs.count i := by simp [List.count_cons, hc]
      rw [h3]
      exact ih.fd_any c

theorem lineDeg_coneTerm (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (i : Fin r)
    (p : ℕ) : LineDeg i (Fintype.card ι * p + 1) (coneTerm a b (-(p : ℂ))) := by
  classical
  intro m
  let c : ι → ℂ := fun j => ((b j + ∑ k, a j k * (m k : ℝ) : ℝ) : ℂ)
  refine ⟨∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p, ?_, fun t => ?_⟩
  · have hnd : (∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤
        Fintype.card ι * p := by
      have hj : ∀ j, ((Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤ p := by
        intro j
        calc _ ≤ p * (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ p * 1 := Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le
          _ = p := mul_one p
      refine (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
      simp
    calc _ ≤ _ := Polynomial.degree_le_natDegree
      _ < _ := by exact_mod_cast Nat.lt_succ_of_le hnd
  · rw [Polynomial.eval_prod]
    simp only [coneTerm, neg_neg, Complex.cpow_natCast, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero, mul_add, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    ring

theorem DL_coneTerm_neg_natCast_eq_zero : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  intro ι _ r a b cs i N p hN hlt m
  have h := (lineDeg_coneTerm ι r a b i p).DL cs
  rw [hN, show Fintype.card ι * p + 1 - N = 0 by omega] at h
  exact h.eq_zero m

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
