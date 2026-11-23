import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem not_mem_div_uniformizer_pow : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable

  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨r, rfl⟩
    exact this

  have hKV : ∀ c : K, algebraMap K Ω c ∈ V → ∃ r : R, algebraMap R K r = c := by
    intro c hc
    have : c ∈ V.toSubring.comap (algebraMap K Ω) := hc
    rw [hV] at this
    exact this
  have halgK : IsAlgebraic K x⁻¹ := Algebra.IsAlgebraic.isAlgebraic _
  have halgR : IsAlgebraic R x⁻¹ := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨d, hd0, hint⟩ := halgR.exists_integral_multiple
  let f : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV
  letI : Algebra R V := f.toAlgebra
  haveI : IsScalarTower R V Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintV : IsIntegral V (d • x⁻¹) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  have hyV : d • x⁻¹ ∈ V := by rw [← hy]; exact y.2

  have hfin : FiniteMultiplicity π d := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hd0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ π ^ n ∣ d := by
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m + 1, hm⟩
  refine ⟨n, fun hmem => hn ?_⟩
  have hprod : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) ∈ V := V.mul_mem _ _ hyV hmem
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have heq : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) =
      algebraMap K Ω (algebraMap R K d / algebraMap R K π ^ n) := by
    rw [Algebra.smul_def, map_div₀, map_pow]
    change (algebraMap K Ω) (algebraMap R K d) * x⁻¹ * _ = _
    field_simp
  rw [heq] at hprod
  obtain ⟨r, hr⟩ := hKV _ hprod
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_pow, hr]
  field_simp

end GlobalTheory
