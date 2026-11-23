import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Local

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem int_mem_regAt (hN : NormalCpt ξ) (φ : F →+* Ω) (a : 𝓞 F) (q : Cpt ξ) : φ (a : F) ∈ regAt ξ q :=
  hN q _ ((map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)).tower_top)

theorem overInt_of_normalCpt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
    (ht : CoordTie ℤ ξ fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) (hN : NormalCpt ξ) (φ : F →+* Ω) :
    OverInt y φ := by
  refine ⟨fun k => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩
  · have hc' : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 := (ht.ring c hc' (φ (a : F))).2 fun p _ => int_mem_regAt hN φ a p
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩

theorem cst_mem_regAt_of_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) (a : F) :
    φ a ∈ regAt ξ p := by
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hu := hp n hn
  have h1 : φ (n • a) ∈ regAt ξ p := int_mem_regAt hN φ (⟨n • a, hi⟩ : 𝓞 F) p
  have h2 : φ a = (algebraMap ℤ Ω n)⁻¹ * φ (n • a) := by
    rw [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, inv_mul_cancel_left₀]
    simpa using hu.1
  rw [h2]
  exact mul_mem hu.2.2 h1

theorem exists_place_of_notMem_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∉ genFibre ℤ ξ) :
    ∃ v : HeightOneSpectrum (𝓞 F), ∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p := by
  have := Centre.Sep.isLocalRing_regAt ξ p
  let f : 𝓞 F →+* regAt ξ p :=
    (φ.comp (algebraMap (𝓞 F) F)).codRestrict (regAt ξ p) fun a => int_mem_regAt hN φ a p
  have hf : ∀ a : 𝓞 F, ((f a : regAt ξ p) : Ω) = φ (a : F) := fun _ => rfl
  have hmem : ∀ a : 𝓞 F, a ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ↔ ¬ unitAt ξ p (φ (a : F)) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Centre.Sep.isUnit_regAt_iff, hf]
  obtain ⟨o, ho, hu⟩ : ∃ o : ℤ, o ≠ 0 ∧ ¬ unitAt ξ p (algebraMap ℤ Ω o) := by
    by_contra h
    push_neg at h
    exact hp h
  have hne : (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ≠ ⊥ := by
    intro hbot
    have h1 : (o : 𝓞 F) ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f := by
      rw [hmem]
      simpa using hu
    rw [hbot, Ideal.mem_bot] at h1
    exact ho (by exact_mod_cast h1)
  refine ⟨⟨_, inferInstance, hne⟩, fun a ha => ?_⟩
  obtain ⟨n, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hd : unitAt ξ p (φ ((d : 𝓞 F) : F)) := by
    by_contra h
    exact d.2 ((hmem _).2 h)
  have h2 : φ a = φ (n : F) * (φ ((d : 𝓞 F) : F))⁻¹ := by
    have e' : a * ((d : 𝓞 F) : F) = (n : F) := e
    rw [← e', map_mul, mul_inv_cancel_right₀ hd.1]
  rw [h2]
  exact mul_mem (int_mem_regAt hN φ n p) hd.2.2

end Local

end GlobalTheory.CompanionTheory.Ar.Flat
