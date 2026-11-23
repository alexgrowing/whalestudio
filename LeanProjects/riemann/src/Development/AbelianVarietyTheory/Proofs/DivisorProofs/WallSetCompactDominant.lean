import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

variable {ι : Type} {N : ℕ}

theorem isClosed_wallSet (j : ℕ) (τ₀ : ι) (c : ℝ) : IsClosed (wallSet (N := N) j τ₀ c) := by
  unfold wallSet GapZero
  simp only [Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun τ => isClosed_iInter fun i =>
      isClosed_le (by fun_prop) continuous_const
  · exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)

theorem isCompact_wallSet (j : ℕ) (τ₀ : ι) (c : ℝ) : IsCompact (wallSet (N := N) j τ₀ c) := by
  have h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : Fin N =>
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine h.of_isClosed_subset (isClosed_wallSet j τ₀ c) ?_
  intro x hx τ _ i _
  exact abs_le.mp (hx.1 τ i)

theorem dom_of_mem_wallSet (j : ℕ) (τ₀ : ι) {c : ℝ} (hc : 0 ≤ c) {lam : ι → Fin N → ℝ}
    (h : lam ∈ wallSet (N := N) j τ₀ c) : Dom lam := by
  intro τ
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → lam τ b ≤ lam τ a := by
    intro a b hab
    by_cases hw : τ = τ₀ ∧ (b : ℕ) = j
    · obtain ⟨rfl, hb⟩ := hw
      exact (h.2.1 a b hab hb).ge
    · have := h.2.2 τ a b hab hw
      linarith
  have key : ∀ (k : ℕ) (a b : Fin N), (b : ℕ) = a + k → lam τ b ≤ lam τ a := by
    intro k
    induction k with
    | zero =>
      intro a b hab
      have : b = a := Fin.ext (by simpa using hab)
      rw [this]
    | succ k ih =>
      intro a b hab
      have hb := b.2
      exact (step ⟨a + k, by omega⟩ b (by simp; omega)).trans (ih a ⟨a + k, by omega⟩ rfl)
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem wallSet_compact_dom_interior :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (τ₀ : ι), 1 ≤ j → j < N → IsCompact (wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ)))) ∧ (∀ lam ∈ wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))), Dom lam) ∧ ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧ (∃ x ∈ U, GapZero j τ₀ x) ∧ ∀ x ∈ U, GapZero j τ₀ x → x ∈ wallSet j τ₀ (1 / (4 * (N : ℝ))) := by
  intro ι _ _ N j τ₀ hj hjN
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨isCompact_wallSet _ _ _, fun lam h => dom_of_mem_wallSet j τ₀ (by positivity) h, ?_⟩
  refine ⟨{x | (∀ τ i, |x τ i| < 1 / 2) ∧ ∀ τ (a b : Fin N), (b : ℕ) = a + 1 →
      ¬ (τ = τ₀ ∧ (b : ℕ) = j) → 1 / (4 * (N : ℝ)) < x τ a - x τ b}, ?_, ?_, ?_⟩
  · simp only [Set.setOf_and, Set.setOf_forall]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
        isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
        isOpen_iInter_of_finite fun b => isOpen_iInter_of_finite fun _ =>
        isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by fun_prop)
  · refine ⟨fun τ i => ((if τ = τ₀ ∧ j ≤ (i : ℕ) then 1 else 0) - ((i : ℕ) : ℝ)) / (3 * N), ⟨?_, ?_⟩, ?_⟩
    · intro τ i
      have hi : ((i : ℕ) : ℝ) < N := by exact_mod_cast i.2
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * N), div_lt_iff₀ (by positivity), abs_lt]
      split_ifs <;> constructor <;> linarith
    · intro τ a b hab hw
      have hb : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
      have hiff : (τ = τ₀ ∧ j ≤ (b : ℕ)) ↔ (τ = τ₀ ∧ j ≤ (a : ℕ)) := by
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_contra h3
          exact hw ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
      simp only [hiff]
      rw [← sub_div, hb]
      have : ∀ t : ℝ, t - ((a : ℕ) : ℝ) - (t - (((a : ℕ) : ℝ) + 1)) = 1 := fun t => by ring
      rw [this]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    · intro a b hab hb
      have hb' : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
      have h1 : ¬ j ≤ (a : ℕ) := by omega
      have h2 : j ≤ (b : ℕ) := by omega
      simp only [h1, h2, hb', and_true, and_false, if_true, if_false]
      ring
  · intro x hx hg
    exact ⟨fun τ i => (hx.1 τ i).le, hg, fun τ a b h1 h2 => (hx.2 τ a b h1 h2).le⟩

end GlobalTheory.FlagPoly
