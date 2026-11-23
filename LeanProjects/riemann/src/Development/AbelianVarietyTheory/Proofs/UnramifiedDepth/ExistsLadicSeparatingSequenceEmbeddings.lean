import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatingSeq

open TeichSeq

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_mul_unit {w : ℝ} {a u : C} (hu : V.Ge 0 u) (hu' : ¬ V.MM u)
    (h : V.Ge w (a * u)) : V.Ge w a := by
  have h0 : V.v u = 0 := le_antisymm (not_lt.1 hu') (by simpa [VF.Ge] using hu)
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, add_zero] at h

theorem ge_pow_pow_sub {t c : C} (ht : V.Ge 0 t) (hc : V.Ge 0 c) (h : V.Ge 1 (t - c)) (n : ℕ) :
    V.Ge n (t ^ V.l ^ n - c ^ V.l ^ n) := by
  have hq : V.Ge 0 ((V.l : C)⁻¹ * (t - c)) := by simpa using h.l_inv_mul
  have hd : (V.l : intRing V) ∣ (⟨t, ht⟩ : intRing V) - ⟨c, hc⟩ :=
    ⟨⟨_, hq⟩, Subtype.ext (by
      show t - c = ((V.l : intRing V) : C) * ((V.l : C)⁻¹ * (t - c))
      rw [SubringClass.coe_natCast, mul_inv_cancel_left₀ VF.l_ne_zero])⟩
  obtain ⟨z, hz⟩ := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hd n)
  have hz' : t ^ V.l ^ n - c ^ V.l ^ n = (z : C) * (V.l : C) ^ n := by
    have := congrArg Subtype.val hz
    simpa [mul_comm] using this
  rw [hz']
  exact VF.Ge.mul_int z.2 (ge_l_pow V n)

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (1 - em a (s n))) ∧ ∀ φ : O →+* C, (∀ x, V.Ge 0 (φ x)) → (∀ a, ∃ x, V.v (em a x - φ x) = 0) → ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (0 - φ (s n)) := by
  intro C _ _ V O _ d _ em hint hfrob ⟨ε, ⟨y0, hε2⟩, hε1, hεP⟩
  have hεpow : ∀ n, (V.l : O) ∣ ε ^ (n + 1) - ε := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : ε ^ (n + 1 + 1) - ε = (ε ^ (n + 1) - ε) * ε + (ε * ε - ε) := by ring
      rw [this]
      exact dvd_add (ih.mul_right _) ⟨y0, hε2⟩
  have hprod : ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → V.Ge 1 ((ψ ε - 1) * ψ ε) := fun ψ hψ => by
    have h1 : (ψ ε - 1) * ψ ε = ψ y0 * (V.l : C) := by
      have := congrArg ψ hε2
      rw [map_sub, map_mul, map_mul, map_natCast] at this
      linear_combination this
    rw [h1]
    exact (hψ y0).mul_int VF.ge_l
  have hnot : ∀ t : C, V.MM t → ¬ V.MM (t - 1) := fun t h1 h2 => by
    have h3 : V.MM (-(t - 1)) := by unfold VF.MM; rw [V.v.map_neg]; exact h2
    have h4 : 0 < V.v (t + -(t - 1)) := V.v.map_lt_add h1 h3
    simp at h4
  refine ⟨fun n => ε ^ V.l ^ n, fun n => ?_, fun a K => ⟨K, fun n hn => ?_⟩,
    fun φ hφ hsep K => ⟨K, fun n hn => ?_⟩⟩
  · have h1 := hεpow (V.l - 1)
    rw [Nat.sub_add_cancel V.l_prime.one_lt.le] at h1
    have h2 := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub h1 n)
    rw [← pow_mul, ← pow_succ'] at h2
    exact h2
  · have h1 : V.Ge 1 (em a ε - 1) :=
      ge_of_mul_unit (hint a ε) (fun h => hnot _ h (hε1 a)) (hprod _ (hint a))
    have h2 := (ge_pow_pow_sub (hint a ε) VF.Ge.one h1 n).neg
    rw [one_pow, neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)
  · have hm : V.MM (φ ε) := by
      by_contra hu
      obtain ⟨a, ha⟩ := ResidueChar.main C V O d em hint hfrob φ hφ (fun x hx => by
        obtain ⟨y, hy⟩ := hεP x hx
        have h1 : φ x * φ ε = φ y * (V.l : C) := by
          have := congrArg φ hy
          rw [map_mul, map_mul, map_natCast] at this
          linear_combination this
        refine mm_of_ge_one V (ge_of_mul_unit (hφ ε) hu ?_)
        rw [h1]
        exact (hφ y).mul_int VF.ge_l)
      obtain ⟨x, hx⟩ := hsep a
      have h2 : 0 < V.v (φ x - em a x) := ha x
      rw [← neg_sub, V.v.map_neg, hx] at h2
      exact lt_irrefl _ h2
    have h1 : V.Ge 1 (φ ε - 0) := by
      rw [sub_zero]
      refine ge_of_mul_unit ((hφ ε).sub VF.Ge.one) (hnot _ hm) ?_
      rw [mul_comm]
      exact hprod φ hφ
    have h2 := (ge_pow_pow_sub (hφ ε) (VF.Ge.zero 0) h1 n).neg
    rw [zero_pow (pow_ne_zero _ V.l_prime.ne_zero), neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)

end GlobalTheory.SeparatingSeq
