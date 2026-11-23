import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyVal

theorem exists_unit_of_pow {R K' : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K'] [Algebra R K']
    [IsFractionRing R K'] {z : K'} {m : ℕ} (hm : 0 < m) (w : Rˣ) (h : z ^ m = algebraMap R K' w) :
    ∃ u : Rˣ, z = algebraMap R K' u := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K') (x := z) hm
    (by rw [h]; exact isIntegral_algebraMap)
  have h1 : r ^ m = w := IsFractionRing.injective R K' (by rw [map_pow, hr, h])
  have h2 : IsUnit r := (isUnit_pow_iff hm.ne').1 (h1 ▸ w.isUnit)
  exact ⟨h2.unit, by simp [hr]⟩

theorem unit_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {R K' : Type} [CommRing R]
    [Field K'] [Algebra R K'] (hi : Function.Injective (algebraMap R K')) (f : K →+* K')
    (hv : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) (y : K) :
    (∃ u : Rˣ, f y = algebraMap R K' u) ↔ p.valuation K y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact (u.isUnit.map (algebraMap R K')).ne_zero (by rw [← hu, map_zero])
    refine eq_one_of_one_le_mul_left ((hv y).1 ⟨_, hu.symm⟩)
      ((hv y⁻¹).1 ⟨(u⁻¹ : Rˣ), by rw [map_units_inv, map_inv₀, hu]⟩) ?_
    rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  · intro h
    have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨r, hr⟩ := (hv y).2 h.le
    obtain ⟨s, hs⟩ := (hv y⁻¹).2 (by rw [map_inv₀, h, inv_one])
    have e : r * s = 1 := hi (by rw [map_mul, hr, hs, ← map_mul, mul_inv_cancel₀ hy, map_one, map_one])
    exact ⟨Units.mkOfMulEqOne r s e, by simp [hr]⟩

theorem valuation_eq_of_isLocGen {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {c c' : K}
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (h : IsLocGen p c I) (h' : IsLocGen p c' I) :
    p.valuation K c = p.valuation K c' := by
  rw [valuation_eq_exp_count p h.1, valuation_eq_exp_count p h'.1, h.2, h'.2]

theorem exists_pow_rel (K : Type) [Field K] [NumberField K] (x : KeyIn K) :
    ∃ (n : ℕ) (k : K), 1 ≤ n ∧ k ≠ 0 ∧ ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K']
      [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K'), KeyPB x' x f →
      KeyIntegral R x' a d → ∃ u : Rˣ, a ^ (8 * n) * algebraMap R K' u = d ^ (4 * n) * f k := by
  obtain ⟨N, hN, κ, hH, hF, hU, -⟩ := GlobalTheory.keyFormulaPow_and_keyDegree.1
  refine ⟨N x.P.g, κ K x, hN _, (κ K x).ne_zero, ?_⟩
  intro R K' _ _ _ _ _ _ f x' a d hPB hInt
  haveI : CharZero K' := (RingHom.charZero_iff f.injective).1 inferInstance
  obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
  have hFx := hF K K' f x x' hPB
  have hHx := hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
  obtain ⟨u, hu, -⟩ := hU R K' xR _ hPBR
  have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
  refine ⟨u, ?_⟩
  rw [← hu, ← hFx, ← hMdet, ← hg]
  exact hHx

theorem integral_section_unit : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (Tl abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)), KeyLocAt x Tl abelian₂ p → ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K'] [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K') (ca cd : K) (ud : Rˣ), (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) → KeyPB x' x f → KeyIntegral R x' a d → IsLocGen p cd abelian₂.I → d = f cd * algebraMap R K' ud → IsLocGen p ca Tl.I → ∃ u : Rˣ, a = f ca * algebraMap R K' u := by
  intro K _ _ x Tl abelian₂ p hloc R K' _ _ _ _ _ _ f x' a d ca cd ud hval hPB hInt hcd hd hca
  obtain ⟨n, k, hn, hk, H⟩ := exists_pow_rel K x
  obtain ⟨K₁, _, _, R₁, _, _, _, _, _, f₁, x₁, a₁, d₁, ca₁, cd₁, ua₁, ud₁, hPB₁, hInt₁, hval₁, ha₁, hd₁, hca₁, hcd₁⟩ := hloc
  obtain ⟨u₁, hu₁⟩ := H R₁ K₁ f₁ x₁ a₁ d₁ hPB₁ hInt₁
  obtain ⟨u, hu⟩ := H R K' f x' a d hPB hInt
  have h1 : p.valuation K (cd₁ ^ (4 * n) * k / ca₁ ^ (8 * n)) = 1 := by
    refine (unit_iff p (IsFractionRing.injective R₁ K₁) f₁ hval₁ _).1 ⟨ua₁ ^ (8 * n) * u₁ * ud₁⁻¹ ^ (4 * n), ?_⟩
    have hfa : f₁ ca₁ ≠ 0 := (map_ne_zero f₁).2 hca₁.1
    have hD : algebraMap R₁ K₁ (ud₁ : R₁) ≠ 0 := (ud₁.isUnit.map (algebraMap R₁ K₁)).ne_zero
    rw [ha₁, hd₁, mul_pow, mul_pow] at hu₁
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_pow, map_units_inv, map_div₀, map_mul, map_pow, map_pow, inv_pow, ← div_eq_mul_inv,
      div_eq_div_iff (pow_ne_zero _ hfa) (pow_ne_zero _ hD)]
    linear_combination -hu₁
  have h2 : p.valuation K (cd ^ (4 * n) * k / ca ^ (8 * n)) = 1 := by
    rw [map_div₀, map_mul, map_pow, map_pow] at h1 ⊢
    rw [valuation_eq_of_isLocGen hca hca₁, valuation_eq_of_isLocGen hcd hcd₁, h1]
  obtain ⟨w, hw⟩ := (unit_iff p (IsFractionRing.injective R K') f hval _).2 h2
  have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
  have hU : algebraMap R K' (u : R) ≠ 0 := (u.isUnit.map (algebraMap R K')).ne_zero
  obtain ⟨t, ht⟩ := exists_unit_of_pow (R := R) (z := a / f ca) (m := 8 * n) (by omega) (w * ud ^ (4 * n) * u⁻¹) (by
    rw [hd, mul_pow] at hu
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_units_inv, ← hw, map_div₀, map_mul, map_pow, map_pow, div_pow, ← div_eq_mul_inv,
      eq_div_iff hU, div_mul_eq_mul_div, div_mul_eq_mul_div, hu]
    ring)
  exact ⟨t, by rw [← ht, mul_div_cancel₀ _ hfa]⟩

end GlobalTheory.KeyVal
