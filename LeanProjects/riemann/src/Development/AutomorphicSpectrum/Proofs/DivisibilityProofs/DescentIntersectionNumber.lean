import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLComapBaseExtension

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_subfield_constants : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F'] (V' : Ideal (MRing ι F')), IsMultiHomogIdeal V' → (∀ (c : ∀ k, ι k) (a : F'), ∃ (n : ℕ) (G : MRing ι F), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V') → ∀ l : List (K → ℤ), intNumL F (V'.comap (MvPolynomial.map (algebraMap F F'))) l = (Module.finrank F F' : ℤ) * intNumL F' V' l := by
  intro K _ _ ι _ F F' _ _ _ _ V' _ hgen l
  have hgood : ∀ (c : ∀ k, ι k) (a : F'), ∃ n, BaseChangeColon.PlField.Good (F := F) V' n c a := by
    intro c a
    obtain ⟨n, G, hG, hmem⟩ := hgen c a
    exact ⟨n, G, hG, hmem⟩
  obtain ⟨n, hn⟩ := BaseChangeColon.PlField.exists_uniform hgood
  have hev : ∀ᶠ m : K → ℤ in Filter.atTop,
      hilbFn (V'.comap (MvPolynomial.map (algebraMap F F'))) m
        = (Module.finrank F F' : ℤ) * hilbFn V' m := by
    filter_upwards [Filter.eventually_ge_atTop
      (fun k : K => ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ))] with m hm
    have hm' : ∀ k, ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ) ≤ m k := fun k => hm k
    have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (Int.natCast_nonneg _) (hm' k)
    have hlt : ∀ k, n * Fintype.card (ι k) < (m k).toNat := by
      intro k
      have := hm' k
      omega
    unfold hilbFn
    rw [if_pos hm0, if_pos hm0,
      BaseChangeColon.PlField.finrank_piece (fun q hq => BaseChangeColon.PlField.lift_form hn hlt hq), Nat.cast_mul]
  have hne : (Module.finrank F F' : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := F')).ne'
  simp only [intNumL, intNum, mixedDiff, List.ofFn_get]
  exact BaseChangeColon.PlField.eventualValue_mul hne (BaseChangeColon.PlField.foldr_eventually _ l hev)

end GlobalTheory.CompanionTheory.Ar.Num
