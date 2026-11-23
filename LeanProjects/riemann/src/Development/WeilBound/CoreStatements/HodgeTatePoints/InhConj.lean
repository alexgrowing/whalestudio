import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

open GroundTheory.FunctionField in

def ffCurve (k K : Type) [Field k] [Field K] [Algebra k K] [IsFunctionField k K] : ACurve K where
  I := Place k K
  v := fun v => v.valuation
  w := fun v => v.deg
  fin := fun x hx => (Place.finite_ord_ne_zero (k := k) x).subset fun v hv h0 => hv (by
    rw [v.valuation_eq_exp_neg_ord hx, h0]; simp)
  prod := fun x _ => by
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_apply, Finsupp.sum] at h
    have e : ∀ v : Place k K, (v.deg : ℤ) * WithZero.log (v.valuation x) =
        -((divisor x : Divisor k K) v * v.deg) := fun v => by
      rw [divisor_apply, Place.ord]; ring
    simp only [e]
    rw [finsum_neg_distrib, finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k K).support), h, neg_zero]
    intro v hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun h0 => hv (by simp only [h0, zero_mul])

private theorem place_nonempty_of_isFunctionField (k K : Type) [Field k] [Field K] [Algebra k K]
    [GroundTheory.FunctionField.IsFunctionField k K] : Nonempty (GroundTheory.FunctionField.Place k K) := by
  obtain ⟨t, ht, -⟩ := GroundTheory.FunctionField.IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hR : IsIntegrallyClosedIn (integralClosure k K).toSubring K := by infer_instance
  have htR : t ∉ (integralClosure k K).toSubring := fun h => ht (IsIntegral.isAlgebraic h)
  obtain ⟨V, hV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn htR
  exact ⟨⟨V, fun h => htV (h ▸ trivial), fun c => hV (isIntegral_algebraMap (x := c))⟩⟩

theorem inh_ff : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 := by
  intro k K _ _ _ _
  refine ⟨ffCurve k K, ⟨Equiv.refl _, fun i => ⟨rfl, rfl⟩⟩, place_nonempty_of_isFunctionField k K, ?_⟩
  intro i x hx
  obtain ⟨v, rfl⟩ : ∃ v : GroundTheory.FunctionField.Place k K, v = i := ⟨i, rfl⟩
  show v.valuation x ≤ 1
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hd := GroundTheory.FunctionField.divisor_eq_zero_of_isAlgebraic hx h0
    have ho : v.ord x = 0 := by
      have e := GroundTheory.FunctionField.divisor_apply (k := k) x v
      rw [hd] at e
      exact e.symm
    rw [v.valuation_eq_exp_neg_ord h0, ho]
    simp

end PositivityTheory.HtPt.Cc
