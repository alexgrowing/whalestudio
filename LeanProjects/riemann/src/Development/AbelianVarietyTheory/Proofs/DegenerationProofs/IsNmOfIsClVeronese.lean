import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem isNm_of_isCl_veronese : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] (t : J → Ω) (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e → M.IsCl z → (∀ i, ∃ k, z k = t i ^ e) → (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔ IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) → (∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k), ∑ i, (c i : Ω) * (t i ^ e / z k) = 1) → M.IsNm t := by
  intro o Ω _ _ _ M J _ t e n z he hcl hk hint hsum
  choose κ hκ using hk
  have hle : ∀ k p, M.Div z k p → Algebra.adjoin o (Set.range fun l => z l / z k) ≤ M.O p :=
    fun k p h => Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact h.2 l)
  have hA : ∀ i p, M.Div z (κ i) p → M.Div t i p := by
    intro i p h
    have h0 : t i ≠ 0 := fun h0 => h.1 (by rw [hκ, h0, zero_pow (by omega)])
    refine ⟨h0, fun j => hle _ _ h ?_⟩
    rw [hκ, hint i h0]
    exact isIntegral_algebraMap (R := Algebra.adjoin o (Set.range fun j => t j / t i))
      (x := ⟨t j / t i, Algebra.subset_adjoin ⟨j, rfl⟩⟩)
  have hB : ∀ p, ∃ i, M.Div z (κ i) p := by
    intro p
    obtain ⟨k, hk⟩ := hcl.1 p
    obtain ⟨c, hc⟩ := hsum k hk.1
    have h1 : IsUnit (∑ i, (⟨c i, hle _ _ hk (c i).2⟩ : M.O p) * ⟨z (κ i) / z k, hk.2 _⟩) := by
      convert isUnit_one
      apply Subtype.ext
      simpa [hκ] using hc
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h1
    exact ⟨i, (hk.div_iff_isUnit _).2 (isUnit_of_mul_isUnit_right hi)⟩
  have hC : ∀ i p, M.Div t i p → M.Div z (κ i) p := by
    intro i p h
    obtain ⟨i', hi'⟩ := hB p
    have h0 : z (κ i) ≠ 0 := by rw [hκ]; exact pow_ne_zero _ h.1
    refine ⟨h0, fun l => ?_⟩
    have h1 := mul_mem (hi'.2 l) (pow_mem (h.2 i') e)
    rwa [div_pow, ← hκ, ← hκ, div_mul_div_cancel₀ hi'.1] at h1
  refine ⟨fun p => (hB p).imp fun i hi => hA i p hi, fun i hi => ?_⟩
  obtain ⟨U, hU, hD, hR⟩ := hcl.2 (κ i) (by rw [hκ]; exact pow_ne_zero _ hi)
  refine ⟨U, hU, hD.trans (Set.ext fun p => ⟨hA i p, hC i p⟩), fun x => ?_⟩
  rw [hR, hκ]
  exact hint i hi x

end GlobalTheory.ZH
