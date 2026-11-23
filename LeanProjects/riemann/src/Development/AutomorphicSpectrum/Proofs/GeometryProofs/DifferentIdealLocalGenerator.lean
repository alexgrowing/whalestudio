import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open scoped nonZeroDivisors

theorem differentIdeal_principal_in_localSubring :
    ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω)
      [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) →
      ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧
        ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  intro F _ _ Ω _ _ R _ σ hσ
  have hinj : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  set I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  let J : FractionalIdeal (𝓞 F)⁰ F := (I : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := by
    simpa [J] using hI0
  have hJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ0
  let σ' : 𝓞 F →+* R := σ.codRestrict R hσ
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal R).comap σ'
  have hP1 : (1 : 𝓞 F) ∉ P := by
    intro h
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa [P] using h
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

  have hex : ∃ x ∈ I, ∃ y ∈ J⁻¹, ∃ u : 𝓞 F, algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F x * y ∧
      u ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hle : J * J⁻¹ ≤ (P : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      have hab : algebraMap (𝓞 F) F x * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← hJ]
        exact FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 hab
      rw [← hu]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨u, hcon x hx b hb u hu, rfl⟩
    have h1 : (1 : F) ∈ (P : FractionalIdeal (𝓞 F)⁰ F) :=
      hle (by rw [hJ]; exact FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw, hw1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : w = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hw1
    exact hP1 (this ▸ hw)
  obtain ⟨x, hx, y, hy, u, hu, huP⟩ := hex
  have hunit : IsUnit (σ' u) := by
    by_contra hnu
    exact huP ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hσu : σ u ≠ 0 := by
    intro h0
    have : σ' u = 0 := Subtype.ext h0
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : u = 0 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hu
    exact hσu (by simp [this])
  refine ⟨x, hx, fun h => hx0 (hinj (by simpa using h)), fun d hd => ?_⟩
  have hdJ : algebraMap (𝓞 F) F d ∈ J := (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have hdy : algebraMap (𝓞 F) F d * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← hJ]
    exact FractionalIdeal.mul_mem_mul hdJ hy
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).1 hdy
  have hrel : d * u = x * v := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_mul, hu, hv]
    ring
  have hrel' : σ d * σ u = σ x * σ v := by rw [← map_mul, ← map_mul, hrel]
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by simpa using h))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : σ u * (w : Ω) = 1 := congrArg Subtype.val hw
  have key : σ d / σ x = σ v * (w : Ω) := by
    rw [div_eq_iff hσx]
    calc σ d = σ d * (σ u * (w : Ω)) := by rw [hw', _root_.mul_one]
      _ = (σ d * σ u) * (w : Ω) := by ring
      _ = σ v * (w : Ω) * σ x := by rw [hrel']; ring
  rw [key]
  exact R.mul_mem (hσ v) w.2

end GlobalTheory.CompanionTheory.Ar
