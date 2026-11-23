import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CongruentCharacters

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  have ha' : (0 : WithTop ℝ) ≤ V.v a := by simpa [VF.Ge] using ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem cancel_unit {u a : C} {w : ℝ} (hu : V.MM (u - 1)) (h : V.Ge w (u * a)) : V.Ge w a := by
  have h0 : V.v u = 0 := by
    have h1 : V.v (1 : C) < V.v (u - 1) := by rw [V.v.map_one]; exact hu
    have h2 := V.v.map_add_eq_of_lt_left h1
    rw [V.v.map_one] at h2
    simpa using h2
  unfold VF.Ge at *
  rwa [V.v.map_mul, h0, zero_add] at h

theorem pow_sub_pow_factor {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (hab : V.MM (a - b)) (n : ℕ) :
    ∃ S : C, a ^ (n + 1) - b ^ (n + 1) = (a - b) * S ∧
      V.MM (S - ((n + 1 : ℕ) : C) * b ^ n) := by
  induction n with
  | zero => exact ⟨1, by ring, by simp [VF.MM]⟩
  | succ n ih =>
    obtain ⟨S, h1, h2⟩ := ih
    refine ⟨a * S + b ^ (n + 1), by linear_combination a * h1, ?_⟩
    have h3 := mm_add (mm_int_mul ha h2)
      (mm_int_mul (VF.Ge.mul_int (VF.ge_natCast (n + 1)) (hb.pow n)) hab)
    convert h3 using 1
    push_cast; ring

theorem eq_zero_of_ge_all {a : C} (h : ∀ n : ℕ, V.Ge n a) : a = 0 := by
  apply (AddValuation.top_iff V.v).1
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := h n
    unfold VF.Ge at this
    rw [hv] at this
    have h' : (n : ℝ) ≤ t := WithTop.coe_le_coe.1 this
    linarith

theorem eq_of_congruent : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  intro C _ V O _ d hd ε ⟨y, hy⟩ hx ψ φ hψ hφ hε hc
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨m, hm⟩ : ∃ m, V.l ^ d = m + 1 := ⟨V.l ^ d - 1, by have := pow_pos hl0 d; omega⟩
  have hq : V.MM ((m + 1 : ℕ) : C) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [← hm, pow_succ, Nat.cast_mul]
    exact mm_int_mul (VF.ge_natCast _) mm_l
  have key : ∀ n : ℕ, ∀ x, V.Ge n (ψ x - φ x) := by
    intro n
    induction n with
    | zero => intro x; simpa using (hψ x).sub (hφ x)
    | succ n ih =>
      have hl : ∀ z, V.Ge ((n + 1 : ℕ) : ℝ) ((V.l : C) * (ψ z - φ z)) := fun z => by
        have := (ih z).l_mul
        convert this using 1
        push_cast; ring
      have hδε : V.Ge ((n + 1 : ℕ) : ℝ) (ψ ε - φ ε) := by
        have e1 := congrArg ψ hy
        have e2 := congrArg φ hy
        simp only [map_sub, map_mul, map_natCast] at e1 e2
        apply cancel_unit (u := ψ ε + φ ε - 1)
        · have := mm_add (mm_add hε hε) (mm_neg (hc ε))
          convert this using 1; ring
        · convert hl y using 1
          linear_combination e1 - e2
      intro x
      obtain ⟨z, hz⟩ := hx x
      have e1 := congrArg ψ hz
      have e2 := congrArg φ hz
      simp only [map_sub, map_mul, map_natCast, map_pow, hm] at e1 e2
      obtain ⟨S, hS1, hS2⟩ := pow_sub_pow_factor (hψ x) (hφ x) (hc x) m
      have hS : V.MM S := by
        have := mm_add hS2 (mm_int_mul ((hφ x).pow m) hq)
        convert this using 1; ring
      have ht : V.Ge 0 (φ x ^ (m + 1) - φ x) := ((hφ x).pow _).sub (hφ x)
      apply cancel_unit (u := 1 - S)
      · have := mm_neg hS
        convert this using 1; ring
      apply cancel_unit hε
      have := (VF.Ge.mul_int ht hδε).sub (hl z)
      convert this using 1
      linear_combination ψ ε * hS1 - e1 + e2
  ext x
  exact sub_eq_zero.1 (eq_zero_of_ge_all fun n => key n x)

end GlobalTheory.CongruentCharacters
