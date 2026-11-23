import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.CobLin

theorem powerSeriesEvalTwoGroups_sub {R : Type} [CommRing R] {d : ℕ} {τ : Type} (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  exact subst_sub (hasSubst_of_constantCoeff_zero fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s) c c'

theorem constantCoeff_op_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 := by
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hμ i)

theorem sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧
    swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  intro R _ d μ hμ c c' f f'
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · unfold cob2
    rw [powerSeriesEvalTwoGroups_sub c c' _ _ h2 h3, powerSeriesEvalTwoGroups_sub c c' _ _ (constantCoeff_op_eq_zero hμ _ _ h1 h2) h3,
      powerSeriesEvalTwoGroups_sub c c' _ _ h1 (constantCoeff_op_eq_zero hμ _ _ h2 h3), powerSeriesEvalTwoGroups_sub c c' _ _ h1 h2]
    abel
  · unfold swap
    exact powerSeriesEvalTwoGroups_sub c c' _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  · unfold cob1 inL inR
    rw [subst_sub (hasSubst_of_constantCoeff_zero hμ),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    abel

end GlobalTheory.CobLin
