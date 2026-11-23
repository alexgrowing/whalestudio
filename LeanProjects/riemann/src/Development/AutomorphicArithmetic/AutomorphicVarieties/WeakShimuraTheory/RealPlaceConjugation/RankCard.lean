import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.rank_le_of_card_le_pow_card_field :
    ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] (n : ℕ), CardLe W (Nat.card k ^ n) → Module.rank k W ≤ n := by
  intro k W _ _ _ _ n hW
  obtain ⟨hfin, hle⟩ := hW
  haveI := hfin
  haveI : Module.Finite k W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k)] at hle
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hr : Module.finrank k W ≤ n := (Nat.pow_le_pow_iff_right hk).1 hle
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hr
