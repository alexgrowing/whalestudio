import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalizationOfLeClosure
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayReg
open NumberField

theorem isDedekindDomain_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine GlobalTheory.CycAway.isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _

theorem isDedekindDomain_cycAway_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsDedekindDomain (cycAway n) := by
  haveI : NeZero n := ⟨hn⟩
  let K := CyclotomicField n ℚ
  let φ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hz : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta n ℚ K)) n := hζ.map_of_injective φ.injective
  have he : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨k, hk, hkc⟩ := hz.eq_pow_of_pow_eq_one he.pow_eq_one
  have hζk := hζ.pow_of_coprime k (hz.pow_iff_coprime (Nat.pos_of_ne_zero hn) k |>.1 (hkc ▸ he))
  have := isDedekindDomain_closure φ hζk
  rwa [map_pow, hkc] at this

theorem isDedekindDomain_cycAway (n : ℕ) : IsDedekindDomain (cycAway n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : cycAway 0 = cycAway 1 := by
      have hb : ∀ m : ℕ, m ≤ 1 → cycAway m = ⊥ := by
        intro m hm
        refine le_antisymm (Subring.closure_le.2 ?_) bot_le
        rintro _ (rfl | rfl)
        · interval_cases m <;> simp [zeta]
        · interval_cases m <;> simp
      rw [hb 0 zero_le_one, hb 1 le_rfl]
    rw [h]
    exact isDedekindDomain_cycAway_of_ne_zero one_ne_zero
  · exact isDedekindDomain_cycAway_of_ne_zero hn.ne'

end GlobalTheory.CycAwayReg

namespace GlobalTheory.CycAwayReg

theorem smooth_over_projective_factorial : ∀ (n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (X : Scheme.{0}) (p : X ⟶ S), IsProjOver s → Smooth s → Smooth p → QuasiCompact p → IsLocallyNoetherian X ∧ CompactSpace X ∧ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro n S s X p hproj hs hp hq
  haveI : IsDedekindDomain (cycAway n) := isDedekindDomain_cycAway n
  haveI : IsRegularRing (cycAway n) := inferInstance
  haveI : Smooth (p ≫ s) := inferInstance
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (p ≫ s), ?_, fun x => ?_⟩
  · obtain ⟨N, i, hi, hcomp⟩ := hproj
    haveI : IsProper (PSpace.str (cycAway n) N) := isProper_str (cycAway n) N
    haveI : CompactSpace S := by
      rw [← hcomp] at *
      exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (cycAway n) N)
    exact QuasiCompact.compactSpace_of_compactSpace p
  · haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth (cycAway n) (p ≫ s) x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩

end GlobalTheory.CycAwayReg
