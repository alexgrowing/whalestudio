import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unrOfIne :
    UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI
  have hunder : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    ext x
    show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal
    rw [← hw, ← hv]
    have hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K) := by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      rfl
    rw [hx]
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩
  have hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap M Ω).injective
    show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hI t ht x
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← (UpperTheory.V.CF.ineCard).1 K M w, hinert]
    simp
  refine ⟨hunder, ?_, ?_⟩
  · rintro ⟨w', hw'⟩
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]
    exact he
  · intro x hx hmem
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    have hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
      exact he
    have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal :=
      Ideal.map_le_iff_le_comap.2 hcomap.ge
    have hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2 :=
      fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1
    by_cases hxv : x ∈ v.asIdeal
    · obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x} :=
        Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)
      have hJv : ¬ J ≤ v.asIdeal := by
        intro h
        apply hx
        rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
        exact Ideal.mul_mono_right h
      have hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal := by
        intro h
        rw [Ideal.map_le_iff_le_comap, hcomap] at h
        exact hJv h
      have hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤ := by
        by_contra hne
        exact hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))
      have hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤ := by
        have hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal :=
          Ideal.isCoprime_iff_sup_eq.2 hsup
        exact Ideal.isCoprime_iff_sup_eq.1 hc.pow_right
      apply hnot
      have hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
        exact hmem
      have hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2 :=
        Ideal.mul_le_right
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal
          = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal *
              (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2) := by rw [hsup2, Ideal.mul_top]
        _ = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ⊔
              Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 := by
            rw [Ideal.mul_sup, hJ, Ideal.map_mul]
        _ ≤ w.asIdeal ^ 2 := sup_le hx2 hr
    · apply hxv
      rw [← hcomap, Ideal.mem_comap]
      exact Ideal.pow_le_self two_ne_zero hmem
