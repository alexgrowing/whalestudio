import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_polynomial_defect : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  intro R X _ _ _ _ w π π' h
  have key : ∀ k : ℕ, 1 ≤ k → ∀ mu mu' α : X,
      2 * (k : R) * (w (mu + mu') α - w mu α - w mu' α)
        + 2 * (k : R) ^ 2 * (π (mu + mu') - π mu - π mu' - w mu' mu)
        + 2 * (k : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
    intro k hk mu mu' α
    have e := h k hk mu mu' α
    simp only [map_add, map_nsmul, nsmul_eq_mul] at e
    linear_combination e
  have hAB : ∀ mu mu' : X, π (mu + mu') - π mu - π mu' - w mu' mu = 0 ∧
      π' (mu + mu') - π' mu - π' mu' = 0 := by
    intro mu mu'
    have h1 := key 1 le_rfl mu mu' 0
    have h2 := key 2 (by norm_num) mu mu' 0
    simp only [map_zero] at h1 h2
    push_cast at h1 h2
    have h4 : (4 : R) * (π (mu + mu') - π mu - π mu' - w mu' mu) = 0 := by
      linear_combination h2 - 2 * h1
    have hA : π (mu + mu') - π mu - π mu' - w mu' mu = 0 :=
      (mul_eq_zero.mp h4).resolve_left (by norm_num)
    refine ⟨hA, ?_⟩
    have h2' : (2 : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
      linear_combination h1 - 2 * hA
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  have hw : ∀ mu mu' α : X, w (mu + mu') α = w mu α + w mu' α := by
    intro mu mu' α
    have e := key 1 le_rfl mu mu' α
    obtain ⟨hA, hB⟩ := hAB mu mu'
    push_cast at e
    have e2 : (2 : R) * (w (mu + mu') α - w mu α - w mu' α) = 0 := by
      linear_combination e - 2 * hA - 2 * hB
    have := (mul_eq_zero.mp e2).resolve_left (by norm_num)
    linear_combination this
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro mu mu'
    have a := (hAB mu mu').1
    have b := (hAB mu' mu).1
    rw [add_comm mu' mu] at b
    linear_combination a - b
  · intro mu mu'
    linear_combination (hAB mu mu').2
  · intro mu mu'
    linear_combination (hAB mu mu').1

end GlobalTheory
