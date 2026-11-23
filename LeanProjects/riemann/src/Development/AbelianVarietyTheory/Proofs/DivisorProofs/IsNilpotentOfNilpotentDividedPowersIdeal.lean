import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
