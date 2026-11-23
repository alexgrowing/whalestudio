import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqExists : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
      CompleteSpace H ∧ Nontrivial H ∧
      IsURepOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      IsIrredOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      (∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (muG ε)) ∧
      (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lam + rhoN ε - rhoC ε) S) ∧
      ∀ (μ : Fin N → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
        nsq (lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε)

theorem discreteSeriesUpqExists_iff : DiscreteSeriesUpqExists ↔ GlobalTheory.Mem.Vol.DiscreteSeriesExist := Iff.rfl

theorem discreteSeriesUpqExists_iff_dsExists : DiscreteSeriesUpqExists ↔ GlobalTheory.Dec.DSExists := Iff.rfl

theorem rho_antitone {N : ℕ} (ε : Fin N → Bool) : Antitone (rhoC ε + rhoN ε) := by
  have key : ∀ a : Fin N, rhoC ε a + rhoN ε a =
      (((univ.filter fun b => a < b).card : ℝ) - ((univ.filter fun b => b < a).card : ℝ)) / 2 := by
    intro a
    have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin N => a < b)
      (fun b => ε b = ε a)
    have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin N => b < a)
      (fun b => ε b = ε a)
    rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
    have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
    have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
    push_cast at h1' h2'
    simp only [rhoC, rhoN, ne_eq]
    linarith
  intro a b hab
  simp only [Pi.add_apply, key]
  have h1 : (univ.filter fun c : Fin N => b < c).card ≤ (univ.filter fun c : Fin N => a < c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; exact lt_of_le_of_lt hab hc
  have h2 : (univ.filter fun c : Fin N => c < a).card ≤ (univ.filter fun c : Fin N => c < b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; exact lt_of_lt_of_le hc hab
  have h1' : ((univ.filter fun c : Fin N => b < c).card : ℝ) ≤ (univ.filter fun c : Fin N => a < c).card := by
    exact_mod_cast h1
  have h2' : ((univ.filter fun c : Fin N => c < a).card : ℝ) ≤ (univ.filter fun c : Fin N => c < b).card := by
    exact_mod_cast h2
  linarith

theorem norm_lowest_le_of_cone {N : ℕ} (ε : Fin N → Bool) (lam μ : Fin N → ℝ) (hl : Antitone lam)
    (c : Fin N → Fin N → ℕ) (hc : ∀ a b, c a b ≠ 0 → a < b)
    (hμ : μ = lam + rhoN ε - rhoC ε + ∑ a, ∑ b, (c a b : ℝ) • root a b) :
    nsq (lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε) := by
  set x : Fin N → ℝ := lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε with hx
  set Q : Fin N → ℝ := ∑ a, ∑ b, (c a b : ℝ) • root a b with hQ
  have hxa : Antitone x := by
    have : x = lam + (rhoC ε + rhoN ε) := by
      funext a; simp only [hx, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact hl.add (rho_antitone ε)
  have hroot : ∀ a b, ∑ i, x i * root a b i = x a - x b := by
    intro a b
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hdot : 0 ≤ ∑ i, x i * Q i := by
    have : ∑ i, x i * Q i = ∑ a, ∑ b, (c a b : ℝ) * (x a - x b) := by
      simp only [hQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← hroot]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h : c a b = 0
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hxa (hc a b h).le))
  have hm : μ + (2 : ℝ) • rhoC ε = x + Q := by rw [hμ, hx]; abel
  rw [hm]
  have : nsq (x + Q) = nsq x + 2 * ∑ i, x i * Q i + ∑ i, Q i * Q i := by
    simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : 0 ≤ ∑ i, Q i * Q i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

end GlobalTheory.Published
