import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValUFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormA
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HNm

open IsDedekindDomain IsLocalRing

variable {R F L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]

variable (R F L) in

def OverR (p : Ideal R) : Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : R, 0 ≤ w (algebraMap F L (algebraMap R F x)) ∧
    (0 < w (algebraMap F L (algebraMap R F x)) ↔ x ∈ p)}

variable (F) in

noncomputable def fz (w : AddValuation L (WithTop ℤ)) : ℕ :=
  letI := resAlg (F := F) w
  Module.finrank (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w))

theorem local_norm [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (y : L) (hy : y ≠ 0) :
    (OverR R F L p).Finite ∧ ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      Algebra.norm F y * algebraMap R F s = algebraMap R F g ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ OverR R F L p),
          (fz F w : ℤ) * WithTop.untopD 0 (w y)) * algebraMap R F a := by
  classical
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap R F s) := fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (fun h0 => Ideal.mem_primeCompl_iff.mp s.2 (by rw [h0]; exact p.zero_mem)))
  letI : Algebra (Localization.AtPrime p) F :=
    (IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) F := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) (S := Localization.AtPrime p) hunit x).symm)
  haveI : IsFractionRing (Localization.AtPrime p) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl (Localization.AtPrime p) F
  letI : Algebra (Localization.AtPrime p) L :=
    ((algebraMap F L).comp (algebraMap (Localization.AtPrime p) F)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime p) F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) L := IsScalarTower.of_algebraMap_eq
    (fun x => congrArg (algebraMap F L)
      (IsLocalization.lift_eq (M := p.primeCompl) (S := Localization.AtPrime p) hunit x).symm)
  have hset : OverR R F L p = ValPl.PlacesOver (Localization.AtPrime p) L := by
    ext w
    simp only [OverR, ValPl.PlacesOver, Set.mem_setOf_eq]
    exact and_congr_right fun _ => ValPl.placesOver_iff_loc (R := R) (O := Localization.AtPrime p) (L := L) p w
  haveI : IsDedekindDomain (integralClosure (Localization.AtPrime p) L) :=
    integralClosure.isDedekindDomain (Localization.AtPrime p) F L
  haveI : IsFractionRing (integralClosure (Localization.AtPrime p) L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := Localization.AtPrime p) (K := F) (L := L)
  obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_places (O := Localization.AtPrime p) (F := F) (L := L) y hy hirr
  obtain ⟨⟨a, s⟩, hus⟩ := IsLocalization.mk'_surjective p.primeCompl u
  have hus' : IsLocalization.mk' (Localization.AtPrime p) a s = u := hus
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) a s
  rw [hus'] at hspec
  have hs : (s : R) ∉ p := Ideal.mem_primeCompl_iff.mp s.2
  have ha : a ∉ p := by
    have h1 : IsUnit (algebraMap R (Localization.AtPrime p) a) := by
      rw [← hspec]
      exact hu.mul (IsLocalization.map_units (Localization.AtPrime p) s)
    exact Ideal.mem_primeCompl_iff.mp
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p a).mp h1)
  have e1 : algebraMap (Localization.AtPrime p) F (algebraMap R (Localization.AtPrime p) g) =
      algebraMap R F g := (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F g).symm
  have e2 : algebraMap (Localization.AtPrime p) F u * algebraMap R F (s : R) = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F (s : R),
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) F a, ← map_mul, hspec]
  refine ⟨by rw [hset]; exact ValPl.placesOver_finite (Localization.AtPrime p) (F := F) L, a, s, ha, hs, ?_⟩
  rw [hset, hN, e1, mul_assoc, e2]
  all_goals rfl

theorem fin_support [FiniteDimensional F L] (y : L) (hy : y ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ ∃ w ∈ OverR R F L p, w y ≠ 0}.Finite := by
  classical
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ z : L, IsAlgebraic R z := fun z =>
    (IsFractionRing.isAlgebraic_iff R F L).mpr (Algebra.IsIntegral.isIntegral (R := F) z).isAlgebraic
  obtain ⟨d, hd0, hd⟩ := (halg y).exists_integral_multiple
  obtain ⟨e, he0, he⟩ := (halg y⁻¹).exists_integral_multiple
  have hD0 : d * e ≠ 0 := mul_ne_zero hd0 he0

  have key : ∀ p : Ideal R, (∃ w ∈ OverR R F L p, w y ≠ 0) → d * e ∈ p := by
    rintro p ⟨w, hw, hwy⟩
    simp only [OverR, Set.mem_setOf_eq] at hw
    by_contra hde
    have hdp : d ∉ p := fun h => hde (p.mul_mem_right e h)
    have hep : e ∉ p := fun h => hde (p.mul_mem_left d h)
    have h0 : ∀ r : R, 0 ≤ w (algebraMap R L r) := fun r => (hw.2 r).1
    have hwd : w (algebraMap R L d) = 0 :=
      le_antisymm (not_lt.mp fun h => hdp ((hw.2 d).2.mp h)) (hw.2 d).1
    have hwe : w (algebraMap R L e) = 0 :=
      le_antisymm (not_lt.mp fun h => hep ((hw.2 e).2.mp h)) (hw.2 e).1
    have h1 : 0 ≤ w (d • y) := nonneg_of_isIntegral w h0 hd
    have h2 : 0 ≤ w (e • y⁻¹) := nonneg_of_isIntegral w h0 he
    rw [Algebra.smul_def, AddValuation.map_mul, hwd, zero_add] at h1
    rw [Algebra.smul_def, AddValuation.map_mul, hwe, zero_add] at h2
    have h3 : w y + w y⁻¹ = 0 := by
      rw [← AddValuation.map_mul w y y⁻¹, mul_inv_cancel₀ hy, AddValuation.map_one]
    exact hwy (wt_add_eq_zero h1 h2 h3)
  have hsub : {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ ∃ w ∈ OverR R F L p, w y ≠ 0} ⊆
      (fun q : R => Ideal.span {q}) '' {q | q ∈ UniqueFactorizationMonoid.factors (d * e)} := by
    rintro p ⟨hp, hh, hw⟩
    haveI := hp
    obtain ⟨g, hg, rfl⟩ := ValUFD.heightOne_principal p hh
    have hdvd : g ∣ d * e := Ideal.mem_span_singleton.mp (key _ hw)
    obtain ⟨q, hq, hgq⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hD0 hg.irreducible hdvd
    exact ⟨q, hq, Ideal.span_singleton_eq_span_singleton.mpr hgq.symm⟩
  exact ((Multiset.finite_toSet _).image _).subset hsub

end HNm

end ReciprocityTheory.ChartRestriction.G.T0
