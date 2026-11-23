import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

noncomputable section
namespace GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0

section Base
variable {k F : Type} [Field k] [Field F] [Algebra k F] (Pl : Places k F)

theorem v_one (i : Pl.I) : Pl.v i 1 = 0 := by
  have := Pl.v_mul i 1 1
  rw [mul_one] at this
  omega

theorem v_inv (i : Pl.I) (x : Fˣ) : Pl.v i x⁻¹ = -Pl.v i x := by
  have := Pl.v_mul i x x⁻¹
  rw [mul_inv_cancel, v_one] at this
  omega

theorem v_zpow (i : Pl.I) (x : Fˣ) (n : ℤ) : Pl.v i (x ^ n) = n * Pl.v i x := by
  induction n using Int.induction_on with
  | zero => simp [v_one]
  | succ n ih => rw [zpow_add_one, Pl.v_mul, ih]; ring
  | pred n ih => rw [zpow_sub_one, Pl.v_mul, ih, v_inv]; ring

theorem v_unit (i : Pl.I) {u : Pl.O i} (hu : IsUnit u) (x : Fˣ) (hx : (x : F) = u) : Pl.v i x = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 := (Pl.mem i x).1 (hx ▸ (w : Pl.O i).2)
  have h2 : ((x⁻¹ : Fˣ) : F) = ((w⁻¹ : (Pl.O i)ˣ) : Pl.O i) := by
    rw [Units.val_inv_eq_inv_val, hx]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h3 := (Pl.mem i x⁻¹).1 (h2 ▸ ((w⁻¹ : (Pl.O i)ˣ) : Pl.O i).2)
  rw [v_inv] at h3
  omega

theorem v_pos (i : Pl.I) {u : Pl.O i} (hu : ¬ IsUnit u) (x : Fˣ) (hx : (x : F) = u) : 0 < Pl.v i x := by
  by_contra h
  have h2 : ((x⁻¹ : Fˣ) : F) ∈ Pl.O i := (Pl.mem i x⁻¹).2 (by rw [v_inv]; omega)
  refine hu (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext ?_))
  change (u : F) * ((x⁻¹ : Fˣ) : F) = 1
  rw [← hx, Units.mul_inv]

theorem fin_notMem (x : F) : {i | x ∉ Pl.O i}.Finite := by
  by_cases hx : x = 0
  · subst hx; simp
  · refine (Pl.fin (Units.mk0 x hx)).subset fun i hi h => hi ?_
    exact (Pl.mem i (Units.mk0 x hx)).2 (le_of_eq (Eq.symm h))

theorem fin_notIntegral {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] (y : L) :
    {i | ¬ IsIntegral (Pl.O i) y}.Finite := by
  have hy : IsIntegral F y := IsIntegral.of_finite F y
  refine ((minpoly F y).support.finite_toSet.biUnion
    fun n _ => fin_notMem Pl ((minpoly F y).coeff n)).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, not_exists, Set.mem_setOf_eq, not_not] at hc
  apply hi
  have hl : minpoly F y ∈ lifts (algebraMap (Pl.O i) F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ (minpoly F y).support
    · exact ⟨⟨_, hc n hn⟩, rfl⟩
    · rw [notMem_support_iff.1 hn]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
  refine ⟨q, hm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]

end Base

section Ext
variable {k F L : Type} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] (Pl : Places k F)

variable (L) in

theorem exists_local (i : Pl.I) [IsDiscreteValuationRing (Pl.O i)] :
    ∃ (J : Type) (_ : Finite J) (O' : J → ValuationSubring L) (w : J → Lˣ → ℤ),
      (∀ j x y, w j (x * y) = w j x + w j y) ∧ (∀ j (x : Lˣ), (x : L) ∈ O' j ↔ 0 ≤ w j x) ∧
      (∀ y : L, (∀ j, y ∈ O' j) ↔ IsIntegral (Pl.O i) y) ∧
      ∀ y : Lˣ, ∑ᶠ j, w j y = Pl.v i (Units.map (Algebra.norm F) y) := by
  obtain ⟨hD, hFin, -, -, hmax, -⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank (Pl.O i) F L
  haveI := hD
  haveI := hFin
  haveI : IsFractionRing (integralClosure (Pl.O i) L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Pl.O i) F L _
  haveI : Finite {Q : Ideal (integralClosure (Pl.O i) L) // Q.IsMaximal} := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure (Pl.O i) L)) :=
    Finite.of_equiv _ (ValPl.hoEquiv (Pl.O i) F L).symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Pl.O i)
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have he : 0 < Pl.v i (Units.mk0 _ hϖ0) := v_pos Pl i hϖ.not_isUnit _ rfl
  refine ⟨HeightOneSpectrum (integralClosure (Pl.O i) L), inferInstance,
    fun P => (P.valuation L).valuationSubring,
    fun P y => ((P.asIdeal.inertiaDeg (Pl.O i) : ℤ) * -WithZero.log (P.valuation L y)) *
      Pl.v i (Units.mk0 _ hϖ0), fun P x y => ?_, fun P x => ?_, fun y => ⟨fun h => ?_, fun h P => ?_⟩,
    fun y => ?_⟩
  · beta_reduce
    rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 x.ne_zero)
      ((Valuation.ne_zero_iff _).2 y.ne_zero)]
    ring
  · have hx : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    haveI := P.isPrime
    have hf : (0 : ℤ) < P.asIdeal.inertiaDeg (Pl.O i) := by
      exact_mod_cast Ideal.inertiaDeg_pos P.asIdeal (Pl.O i)
    rw [Valuation.mem_valuationSubring_iff, ← WithZero.log_le_log hx one_ne_zero, WithZero.log_one,
      mul_nonneg_iff_of_pos_right he, mul_nonneg_iff_of_pos_left hf, neg_nonneg]
  · obtain ⟨b, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := integralClosure (Pl.O i) L) L y h
    exact b.2
  · exact P.valuation_le_one (K := L) (⟨y, h⟩ : integralClosure (Pl.O i) L)
  · obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_heightOne (O := Pl.O i) (F := F) (y : L) y.ne_zero hϖ
    have hu0 : (u : F) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
    simp only [ValPl.addv_apply _ y.ne_zero, WithTop.untopD_coe] at hN
    have : Units.map (Algebra.norm F) y = Units.mk0 _ hϖ0 ^ (∑ᶠ P : HeightOneSpectrum (integralClosure (Pl.O i) L),
        ((P.asIdeal.inertiaDeg (Pl.O i) : ℤ) * -WithZero.log (P.valuation L y))) * Units.mk0 _ hu0 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
      exact hN
    rw [this, Pl.v_mul, v_zpow, v_unit Pl i hu (Units.mk0 _ hu0) rfl, add_zero, finsum_mul' _ _ (Set.toFinite _)]

variable (L) in

theorem exists_ext [Algebra k L] [IsScalarTower k F L] (hD : ∀ i, IsDiscreteValuationRing (Pl.O i)) :
    ∃ Pl' : Places k L, ∀ y : L, (∀ j, y ∈ Pl'.O j) → ∀ i, IsIntegral (Pl.O i) y := by
  classical
  choose J hJ O' w hmul hmem hint hsum using fun i => exists_local L Pl i
  have hone : ∀ i j, w i j 1 = 0 := fun i j => by
    have := hmul i j 1 1
    rw [mul_one] at this
    omega
  have hT : ∀ y : Lˣ, ∃ T : Finset Pl.I, ∀ i ∉ T, ∀ j, w i j y = 0 := fun y => by
    refine ⟨((fin_notIntegral Pl (y : L)).union (fin_notIntegral Pl ((y⁻¹ : Lˣ) : L))).toFinset,
      fun i hi j => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hi
    have h1 := (hmem i j _).1 ((hint i _).2 hi.1 j)
    have h2 := (hmem i j _).1 ((hint i _).2 hi.2 j)
    have h3 := hmul i j y y⁻¹
    rw [mul_inv_cancel, hone] at h3
    omega
  haveI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite _
  have hsupp : ∀ (y : Lˣ) (T : Finset Pl.I), (∀ i ∉ T, ∀ j, w i j y = 0) →
      (Function.support fun p : Σ i, J i => w p.1 p.2 y) ⊆
        ((T.sigma fun _ => Finset.univ : Finset (Σ i, J i)) : Set _) := fun y T h p hp => by
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true]
    by_contra hc
    exact hp (h _ hc _)
  refine ⟨⟨Σ i, J i, fun p => O' p.1 p.2, fun p => w p.1 p.2, fun p => hmul p.1 p.2,
    fun p => hmem p.1 p.2, fun p c => ?_, fun y => ?_, fun y => ?_⟩,
    fun y hy i => (hint i y).1 fun j => hy ⟨i, j⟩⟩
  · refine (hint p.1 _).2 ?_ p.2
    rw [IsScalarTower.algebraMap_apply k F L]
    exact isIntegral_algebraMap (x := (⟨_, Pl.const p.1 c⟩ : Pl.O p.1))
  · obtain ⟨T, h⟩ := hT y
    exact (Finset.finite_toSet _).subset (hsupp y T h)
  · obtain ⟨T, h⟩ := hT y
    rw [finsum_eq_sum_of_support_subset _ (hsupp y T h), Finset.sum_sigma,
      ← Pl.sum (Units.map (Algebra.norm F) y), finsum_eq_sum_of_support_subset (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hsum, finsum_eq_sum_of_fintype]
    · intro i hi
      by_contra hc
      apply hi
      simp only [← hsum, h i hc, finsum_zero]

theorem isAlgebraic_of_forall [Algebra k L] [IsScalarTower k F L]
    (hc : ∀ c : F, (∀ i, c ∈ Pl.O i) → c ∈ Set.range (algebraMap k F)) (y : L)
    (hy : ∀ i, IsIntegral (Pl.O i) y) : IsAlgebraic k y := by
  have hyF : IsIntegral F y := IsIntegral.of_finite F y
  have hl : minpoly F y ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine hc _ fun i => ?_
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F (hy i), coeff_map]
    exact ((minpoly (Pl.O i) y).coeff n).2
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hm.ne_zero, ?_⟩
  rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

end Ext

section Line
variable (k : Type) [Field k]

theorem projLine_dvr (i : (projLinePlaces k).I) : IsDiscreteValuationRing ((projLinePlaces k).O i) := by
  classical
  cases i with
  | none =>
    change IsDiscreteValuationRing (RatFunc.inftyValuation k).valuationSubring
    infer_instance
  | some p =>
    change IsDiscreteValuationRing (p.prime.valuation (RatFunc k)).valuationSubring
    infer_instance

theorem projLine_const (c : RatFunc k) (h : ∀ i, c ∈ (projLinePlaces k).O i) :
    c ∈ Set.range (algebraMap k (RatFunc k)) := by
  classical
  obtain ⟨p, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := k[X]) (RatFunc k) c fun v => by
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact v.ne_bot (by simpa using hg)
    have hg' : v.asIdeal = Ideal.span {g} := hg
    have hp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg' ▸ v.isPrime)
    have hn : Associated (normalize g) g := normalize_associated g
    let π : MonIrr k := ⟨normalize g, monic_normalize hg0, hn.symm.irreducible hp.irreducible⟩
    have : π.prime = v := HeightOneSpectrum.ext
      ((Ideal.span_singleton_eq_span_singleton.2 hn).trans hg'.symm)
    rw [← this]
    exact h (some π)
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hp' : algebraMap k[X] (RatFunc k) p ≠ 0 := by simpa using hp
  have h1 : 0 ≤ plOrd k none (algebraMap k[X] (RatFunc k) p) :=
    ((projLinePlaces k).mem none (Units.mk0 _ hp')).1 (h none)
  rw [plOrd_none hp] at h1
  have h2 : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), algebraMap_eq, ← eq_C_of_natDegree_eq_zero h2]

end Line

theorem exists_places : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t →
    FiniteDimensional (IntermediateField.adjoin k {t}) K →
    Algebra.IsSeparable (IntermediateField.adjoin k {t}) K →
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by
  intro k K _ _ _ t ht hf hs
  let e := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc k) K :=
    ((algebraMap (IntermediateField.adjoin k {t}) K).comp e.toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower k (RatFunc k) K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap (IntermediateField.adjoin k {t}) K (e (algebraMap k _ c))
    rw [e.commutes]; rfl
  have H : RingHom.comp (algebraMap (RatFunc k) K) (e.symm.toRingEquiv : _ →+* _) =
      RingHom.comp (RingEquiv.refl K : K →+* K) (algebraMap (IntermediateField.adjoin k {t}) K) := by
    ext x
    change algebraMap (IntermediateField.adjoin k {t}) K (e (e.symm x)) = _
    rw [e.apply_symm_apply]; rfl
  haveI : FiniteDimensional (RatFunc k) K := Module.Finite.of_equiv_equiv _ _ H
  haveI : Algebra.IsSeparable (RatFunc k) K := Algebra.IsSeparable.of_equiv_equiv _ _ H
  obtain ⟨Pl, hPl⟩ := exists_ext K (projLinePlaces k) (projLine_dvr k)
  exact ⟨Pl, fun x hx => isAlgebraic_of_forall (projLinePlaces k) (projLine_const k) x (hPl x hx)⟩

end GlobalTheory.SS.PlacesExt
end
