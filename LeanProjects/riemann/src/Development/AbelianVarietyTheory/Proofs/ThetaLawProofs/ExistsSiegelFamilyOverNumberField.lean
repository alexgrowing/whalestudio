import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SiegelFamilyNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
open NumberField Polynomial in

theorem _root_.GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange {h k : ℕ} {o B : Type} [CommRing o] [CommRing B] {ζ : o}
    (F : _root_.GlobalTheory.ZM.SFam h k ζ)
    (j : o →+* B) (hinj : Function.Injective j) : Nonempty (_root_.GlobalTheory.ZM.SFam h k (j ζ)) := by
  obtain ⟨hex, hprin, -⟩ := _root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h k o B ζ (j ζ) j F.X
    (pullback F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) F.s (pullback.snd F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) (pullback.fst F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j))
    rfl pullback.condition
  obtain ⟨U, hU⟩ := hex F.univ
  have hsmooth : SmoothOfRelativeDimension (h * (h + 1) / 2) (pullback.snd F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (h * (h + 1) / 2)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (h * (h + 1) / 2))
      (IsPullback.of_hasPullback F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) F.3
  refine ⟨⟨pullback F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j), pullback.snd F.s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j), hsmooth,
    (_root_.GlobalTheory.isQProjOver_baseChange_and_finite_restrict o B j F.X F.s).1 F.4, U,
    hprin F.univ U hU F.6, ?_, ?_⟩⟩
  · intro S s' c hS hdense hc
    refine _root_.GlobalTheory.SiegelFamilyBaseChange.rep_baseChange F j rfl U hU s' c hS (hdense.mono ?_) hc
    intro x hx
    change Ideal.comap j (s' x).asIdeal = ⊥
    rw [show (s' x).asIdeal = ⊥ from hx]
    exact Ideal.comap_bot_of_injective j hinj
  · intro R _ _ x y s' c hxy hx hy
    exact _root_.GlobalTheory.SiegelFamilyBaseChange.inj_baseChange F j rfl U hU x y s' c hxy hx hy

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
open NumberField Polynomial in
private theorem isPrimitiveRoot_map_localization_away (k : ℕ) (hk : 0 < k) (K : Type) [Field K]
    [NumberField K] (ζ : 𝓞 K) (hζ : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) k)
    (L : Type) [Field L] (β : Localization.Away (k : 𝓞 K) →+* L) :
    IsPrimitiveRoot (β (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K)) ζ)) k := by
  have hζO : IsPrimitiveRoot ζ k := hζ.of_map_of_injective (IsFractionRing.injective (𝓞 K) K)
  have hunit : IsUnit (β (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K)) (k : 𝓞 K))) :=
    (IsLocalization.Away.algebraMap_isUnit (k : 𝓞 K)).map β
  have hkL : ((k : ℕ) : L) ≠ 0 := by
    simpa using hunit.ne_zero
  haveI : NeZero ((k : ℕ) : L) := ⟨hkL⟩
  set g : 𝓞 K →+* L := β.comp (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K)))
  have hroot : IsRoot (cyclotomic k (𝓞 K)) ζ := hζO.isRoot_cyclotomic hk
  have : IsRoot (cyclotomic k L) (g ζ) := by
    rw [← map_cyclotomic k g, IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hroot.eq_zero,
      map_zero]
  exact (isRoot_cyclotomic_iff).mp this

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
open NumberField Polynomial in

theorem _root_.GlobalTheory.SiegelFamilyNumberField.exists_sFam_numberField : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV → ∀ h : ℕ, 1 ≤ h → ∃ (k : ℕ) (K : Type) (_ : Field K) (_ : NumberField K) (ζ : K) (σ : K →+* ℂ), 3 ≤ k ∧ Odd k ∧ σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) ∧ Nonempty (_root_.GlobalTheory.ZM.SFam h k ζ) := by
  intro hL hL2 hT h hh
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hL hL2
    _root_.GlobalTheory.Moduli.cube_of_isLB hT h 3 hh Nat.prime_three ⟨1, rfl⟩
  have hkpos : 0 < (3 ^ max j₀ 1) ^ 2 := by positivity
  haveI : NeZero ((3 ^ max j₀ 1) ^ 2) := ⟨hkpos.ne'⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := (3 ^ max j₀ 1) ^ 2)
  haveI : NumberField ↥(_root_.GlobalTheory.ZM.CycBase.CF ((3 ^ max j₀ 1) ^ 2)) :=
    IsCyclotomicExtension.numberField {(3 ^ max j₀ 1) ^ 2} ℚ _
  have hprim : IsPrimitiveRoot (_root_.GlobalTheory.ZM.CycBase.zF ((3 ^ max j₀ 1) ^ 2)) ((3 ^ max j₀ 1) ^ 2) :=
    _root_.GlobalTheory.ZM.CycBase.zF_prim hkpos.ne'
  set k := (3 ^ max j₀ 1) ^ 2 with hk
  set K := ↥(_root_.GlobalTheory.ZM.CycBase.CF k) with hK
  let ζO : 𝓞 K := ⟨_root_.GlobalTheory.ZM.CycBase.zF k, hprim.isIntegral hkpos⟩
  have hζO : algebraMap (𝓞 K) K ζO = _root_.GlobalTheory.ZM.CycBase.zF k := rfl
  have hprimO : IsPrimitiveRoot ζO k :=
    (hζO ▸ hprim).of_map_of_injective (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨em, hem, -⟩ := _root_.GlobalTheory.ZM.exists_arBase_away
    (_root_.GlobalTheory.ZM.CycBase.CF k).val.toRingHom (n := k) hkpos.ne'
  let b : _root_.GlobalTheory.ZM.TBase (Localization.Away (k : 𝓞 K)) k :=
    ⟨((hprimO.isUnit hkpos.ne').map (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K)))).unit,
      by simpa using IsLocalization.Away.algebraMap_isUnit (k : 𝓞 K),
      fun L _ β => isPrimitiveRoot_map_localization_away k hkpos K ζO (hζO ▸ hprim) L β⟩
  have F0 := hj₀ (max j₀ 1) (le_max_left _ _) (Localization.Away (k : 𝓞 K)) b em hem
  have hunitK : IsUnit (algebraMap (𝓞 K) K (k : 𝓞 K)) := by
    rw [map_natCast]
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hkpos.ne')
  let emb : Localization.Away (k : 𝓞 K) →+* K := IsLocalization.Away.lift (k : 𝓞 K) hunitK
  have hinjO : Function.Injective (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K))) :=
    IsLocalization.injective (Localization.Away (k : 𝓞 K))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hkpos.ne'))
  have hemb : Function.Injective emb := by
    refine (IsLocalization.lift_injective_iff _).mpr fun x y => ?_
    rw [hinjO.eq_iff, (IsFractionRing.injective (𝓞 K) K).eq_iff]
  obtain ⟨F1⟩ := _root_.GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange F0.some emb hemb
  refine ⟨k, K, inferInstance, inferInstance, emb ↑b.ζ,
    (starRingEnd ℂ).comp (_root_.GlobalTheory.ZM.CycBase.CF k).val.toRingHom, ?_, ?_, ?_, ⟨F1⟩⟩
  · have h3 : 3 ≤ 3 ^ max j₀ 1 := Nat.le_self_pow (by omega) 3
    have h4 : 3 ^ max j₀ 1 ≤ (3 ^ max j₀ 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · exact (Odd.pow ⟨1, rfl⟩).pow
  · have hb : emb ↑b.ζ = _root_.GlobalTheory.ZM.CycBase.zF k := by
      change emb (algebraMap (𝓞 K) (Localization.Away (k : 𝓞 K)) ζO) = _
      exact (IsLocalization.lift_eq _ _).trans hζO
    rw [RingHom.comp_apply, hb]
    change (starRingEnd ℂ) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) = _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
    rw [← Complex.exp_conj]
    congr 1
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]

end GlobalTheory.SiegelFamilyNumberField
end
