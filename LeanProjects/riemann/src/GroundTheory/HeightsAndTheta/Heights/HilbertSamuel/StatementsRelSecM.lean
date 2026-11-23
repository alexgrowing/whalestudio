import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : Submodule R Ω :=
  Submodule.span R ((fun μ : (Σ k, ι k) → ℕ => ∏ p, y p ^ μ p) '' {μ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k})

theorem monomial_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b : K → ℕ} (μ : (Σ k, ι k) → ℕ)
    (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k) : ∏ p, y p ^ μ p ∈ relSecM R y b :=
  Submodule.subset_span ⟨μ, hμ, rfl⟩

theorem relSecM_fg (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : (relSecM R y b).FG := by
  have hfin : {μ : (Σ k, ι k) → ℕ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k}.Finite := by
    refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (b p.1)) fun p => Set.finite_Iic _).subset ?_
    intro μ hμ p _
    simp only [Set.mem_Iic]
    rw [← hμ p.1]
    exact Finset.single_le_sum (f := fun i => μ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  exact Submodule.fg_span (hfin.image _)

theorem mul_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b b' : K → ℕ} {x x' : Ω}
    (hx : x ∈ relSecM R y b) (hx' : x' ∈ relSecM R y b') : x * x' ∈ relSecM R y (b + b') := by
  have hle : relSecM R y b * relSecM R y b' ≤ relSecM R y (b + b') := by
    rw [relSecM, relSecM, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨μ + ν, fun k => ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hμ k, hν k]
    · simp [pow_add, Finset.prod_mul_distrib]
  exact hle (Submodule.mul_mem_mul hx hx')

theorem adjoin_isNoetherianRing {m : ℕ} (g : Fin m → Ω) : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range g)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  exact Algebra.FiniteType.isNoetherianRing ℤ _

omit [∀ k, Fintype (ι k)] in

theorem mul_prod_mem_relChartLat (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {a a' : K → ℤ} {n : ℕ} (e : K → ℕ)
    (c0 : ∀ k, ι k) (h : ∀ k, a' k = n * a k + e k) {s : Ω} (hs : s ∈ relChartLat R y a n) :
    s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relChartLat R y a' 1 := by
  intro c hc
  have key : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro k
    rw [h k, show -(((1 : ℕ) : ℤ) * ((n : ℤ) * a k + (e k : ℤ))) = -((n : ℤ) * a k) + -((e k : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ (hc k), zpow_neg (y ⟨k, c k⟩) ((e k : ℕ) : ℤ), zpow_natCast]
  rw [Finset.prod_congr rfl fun k _ => key k, Finset.prod_mul_distrib]
  have hmem : (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, (y ⟨k, c0 k⟩ / y ⟨k, c k⟩) ^ e k ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) :=
    mul_mem (hs c hc) (prod_mem fun k _ => pow_mem (Algebra.subset_adjoin
      (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ⟨k, c0 k⟩)) _)
  convert hmem using 1
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Objects

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
