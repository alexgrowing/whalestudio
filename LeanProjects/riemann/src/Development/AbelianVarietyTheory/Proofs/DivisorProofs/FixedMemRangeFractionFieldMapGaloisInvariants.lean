import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem fixed_mem_range : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) →
    y ∈ (fracMap ρ hρ).range := by
  classical
  intro R R' _ _ _ _ ρ hρ hG y hy
  obtain ⟨hfin, hinv⟩ := hG
  letI : Fintype (Gal ρ) := Fintype.ofFinite _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R') y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set P : R' := ∏ σ ∈ (Finset.univ : Finset (Gal ρ)).erase 1, σ.1 b with hP
  set N : R' := ∏ σ : Gal ρ, σ.1 b with hN
  have hNP : N = b * P := by
    rw [hN, hP, ← Finset.mul_prod_erase Finset.univ (fun σ : Gal ρ => σ.1 b) (Finset.mem_univ 1)]
    rfl
  have hσ0 : ∀ σ : Gal ρ, σ.1 b ≠ 0 := fun σ => (map_ne_zero_iff σ.1 σ.1.injective).2 hb0
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hNfix : ∀ τ ∈ Gal ρ, τ N = N := by
    intro τ hτ
    rw [hN, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : Gal ρ)) _ _ (fun σ => rfl)
  obtain ⟨n, hn⟩ := hinv N hNfix
  have inj := IsFractionRing.injective R' (FractionRing R')
  have hPK : algebraMap R' (FractionRing R') P ≠ 0 := (map_ne_zero_iff _ inj).2 hP0
  have hNK : algebraMap R' (FractionRing R') N ≠ 0 := (map_ne_zero_iff _ inj).2 hN0
  have hy' : algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b
      = algebraMap R' (FractionRing R') (a * P) / algebraMap R' (FractionRing R') N := by
    rw [hNP, map_mul, map_mul, mul_div_mul_right _ _ hPK]
  have hcfix : ∀ τ ∈ Gal ρ, τ (a * P) = a * P := by
    intro τ hτ
    apply inj
    have hyN : algebraMap R' (FractionRing R') (a * P)
        = (algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b) * algebraMap R' (FractionRing R') N := by
      rw [hy', div_mul_cancel₀ _ hNK]
    rw [← fracAut_algebraMap, hyN, map_mul, hy ⟨τ, hτ⟩, fracAut_algebraMap, hNfix τ hτ]
  obtain ⟨m, hm⟩ := hinv (a * P) hcfix
  refine ⟨algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) n, ?_⟩
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hm, hn, hy']

end GlobalTheory.Mum.GenDesc
