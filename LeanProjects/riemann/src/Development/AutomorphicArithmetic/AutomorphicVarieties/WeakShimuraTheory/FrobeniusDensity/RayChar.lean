import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.GlobalFields.Artin.OneDim
import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Tw

open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {C : Type} [CommGroup C]

private noncomputable def rcExt (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) : C :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v.asIdeal ^ FractionalIdeal.count K v I

private theorem rcExt_fin (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => f v.asIdeal ^ FractionalIdeal.count K v I).Finite := by
  have h := FractionalIdeal.finite_factors (K := K) I
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv h0 => hv ?_
  simp only [h0, zpow_zero]

private theorem rcExt_mul (f : Ideal (𝓞 K) → C) {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    rcExt f (I * J) = rcExt f I * rcExt f J := by
  unfold rcExt
  rw [← finprod_mul_distrib (rcExt_fin f I) (rcExt_fin f J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul K v hI hJ, zpow_add]

private theorem rcExt_one (f : Ideal (𝓞 K) → C) : rcExt f 1 = 1 := by
  unfold rcExt
  simp only [FractionalIdeal.count_one, zpow_zero, finprod_one]

private theorem rcExt_prime (f : Ideal (𝓞 K) → C) (w : HeightOneSpectrum (𝓞 K)) :
    rcExt f (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = f w.asIdeal := by
  unfold rcExt
  rw [finprod_eq_single _ w]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro v hv
    rw [FractionalIdeal.count_maximal_coprime K v hv.symm, zpow_zero]

private theorem rcExt_coe (𝔪 : Ideal (𝓞 K)) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J)
    (J : Ideal (𝓞 K)) : J ≠ ⊥ → IsCoprime J 𝔪 → rcExt f (J : FractionalIdeal (𝓞 K)⁰ K) = f J := by
  have h1 : f 1 = 1 := by
    have := hm 1 1 one_ne_zero one_ne_zero isCoprime_one_left isCoprime_one_left
    rw [mul_one] at this
    exact left_eq_mul.1 this
  refine UniqueFactorizationMonoid.induction_on_prime J (fun h => absurd rfl h) ?_ ?_
  · intro x hx _ _
    rw [isUnit_iff_eq_one.1 hx, h1, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, rcExt_one]
  · intro a p ha hp ih _ hc
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [FractionalIdeal.coeIdeal_mul, rcExt_mul f (FractionalIdeal.coeIdeal_ne_zero.2 hp0)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), ih ha hc.of_mul_left_right,
      hm p a hp0 ha hc.of_mul_left_left hc.of_mul_left_right]
    congr 1
    exact rcExt_prime f ⟨p, Ideal.isPrime_of_prime hp, hp0⟩

private theorem rc_frac (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (x : K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      v.valuation K x ≤ WithZero.exp (-(multiplicity v.asIdeal 𝔪 : ℤ))) :
    ∃ c d : 𝓞 K, c ≠ 0 ∧ c - 1 ∈ 𝔪 ∧ d ∈ 𝔪 ∧ x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d := by
  let D : Ideal (𝓞 K) :=
    { carrier := {c | ∃ d : 𝓞 K, x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨d, hd⟩ ⟨e, he⟩
        exact ⟨d + e, by rw [map_add, mul_add, hd, he, map_add]⟩
      smul_mem' := by
        rintro r a ⟨d, hd⟩
        exact ⟨r * d, by rw [smul_eq_mul, map_mul, map_mul, ← hd]; ring⟩ }
  have hsup : D ⊔ 𝔪 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    have hv : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
    have h1 : v.valuation K x ≤ 1 := (hx v hv).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer x h1
    exact d.2 (hle (Ideal.mem_sup_left (show (d : 𝓞 K) ∈ D from ⟨n, hd⟩)))
  obtain ⟨c, hc, hc0, hc1⟩ : ∃ c ∈ D, c ≠ 0 ∧ c - 1 ∈ 𝔪 := by
    obtain ⟨c, hc, m, hm, e⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ D ⊔ 𝔪)
    have h1 : c - 1 ∈ 𝔪 := by
      rw [← e, sub_add_cancel_left]; exact 𝔪.neg_mem hm
    by_cases h0 : c = 0
    · obtain ⟨n, d, hd, e'⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      refine ⟨d, ⟨n, ?_⟩, hd0, ?_⟩
      · rw [← e', div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd0
      · have : 𝔪 = ⊤ := by
          rw [h0, zero_add] at e
          exact (Ideal.eq_top_iff_one _).2 (e ▸ hm)
        rw [this]; trivial
    · exact ⟨c, hc, h0, h1⟩
  obtain ⟨d, hd⟩ := hc
  refine ⟨c, d, hc0, hc1, ?_, hd⟩
  rw [← Ideal.iInf_maxPowDividing_eq h𝔪, Submodule.mem_iInf]
  intro v
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity h𝔪]
  by_cases hv : v.asIdeal ∣ 𝔪
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    change v.valuation K (algebraMap (𝓞 K) K d) ≤ _
    rw [← hd, map_mul]
    exact (mul_le_of_le_one_right' (v.valuation_le_one c)).trans (hx v hv)
  · rw [multiplicity_eq_zero.2 hv, pow_zero, Ideal.one_eq_top]; trivial

private theorem rc_cop {𝔪 : Ideal (𝓞 K)} {a : 𝓞 K} (h : a - 1 ∈ 𝔪) : IsCoprime (Ideal.span {a}) 𝔪 := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have : (1 : 𝓞 K) = a - (a - 1) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right h)

private theorem rc_hom (𝔪 : GroundTheory.Global.Modulus K) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪.ideal → IsCoprime J 𝔪.ideal → f (I * J) = f I * f J)
    (h1 : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal → f (Ideal.span {a}) = 1) :
    ∃ F : 𝔪.IdealRayClassGroup →* C, ∀ (w : HeightOneSpectrum (𝓞 K)) (hw : ¬ w.asIdeal ∣ 𝔪.ideal),
      F (𝔪.primeClass hw) = f w.asIdeal := by
  let F₀ : 𝔪.coprimeIdeals →* C :=
    { toFun := fun I => rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      map_one' := rcExt_one f
      map_mul' := fun I J => rcExt_mul f (Units.ne_zero _) (Units.ne_zero _) }
  have key : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal →
      rcExt f (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)) = 1 := fun a ha ha1 => by
    rw [← FractionalIdeal.coeIdeal_span_singleton, rcExt_coe 𝔪.ideal f hm _
      (by rwa [Ne, Ideal.span_singleton_eq_bot]) (rc_cop ha1), h1 a ha ha1]
  refine ⟨QuotientGroup.lift _ F₀ ?_, fun w hw => rcExt_prime f w⟩
  intro I hI
  obtain ⟨a, ha, e⟩ := 𝔪.mem_principalRay.1 hI
  obtain ⟨c, d, hc0, hc1, hd, hcd⟩ := rc_frac 𝔪.ideal 𝔪.ideal_ne_bot ((a : K) - 1) (𝔪.mem_rayUnits.1 ha).1
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc0
  have e2 : (a : K) * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K (c + d) := by
    rw [map_add, ← hcd]; ring
  have hb0 : c + d ≠ 0 := fun h => by
    rw [h, map_zero] at e2
    exact mul_ne_zero a.ne_zero hcK e2
  have hb1 : c + d - 1 ∈ 𝔪.ideal := by
    rw [add_sub_right_comm]; exact Ideal.add_mem _ hc1 hd
  have h3 := key _ hb0 hb1
  rw [← e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    rcExt_mul f (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hcK), key c hc0 hc1, mul_one] at h3
  change rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 1
  rw [← e, coe_toPrincipalIdeal]
  exact h3

end UpperTheory.V.Ws.Tw

theorem UpperTheory.V.Ws.Tw.rayChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → ∀ (C : Type) [CommGroup C] (f : Ideal (𝓞 K) → C), (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J) → (∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪 → f (Ideal.span {a}) = 1) → ∃ κ : G K Ω →* C, IsOpen (κ.ker : Set (G K Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 K), ¬ w.asIdeal ∣ 𝔪 → ∀ A : ValuationSubring Ω, IsPlaceOver A w → Ine (F := K) A ≤ κ.ker ∧ ∀ σ : G K Ω, IsFrob A (normV w) σ → κ σ = f w.asIdeal := by
  intro K Ω _ _ _ _ _ _ 𝔪 h𝔪 C _ f hm h1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let M : GroundTheory.Global.Modulus K := ⟨𝔪, h𝔪, ∅⟩
  obtain ⟨F, hF⟩ := rc_hom M f hm h1
  haveI : NumberField (M.rayClassField Ω) := NumberField.of_module_finite K _
  haveI : Algebra.IsAlgebraic (M.rayClassField Ω) Ω := Algebra.IsAlgebraic.tower_top (K := K) _
  haveI : IsAlgClosure (M.rayClassField Ω) Ω := ⟨inferInstance, inferInstance⟩
  let r : G K Ω →* (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) := AlgEquiv.restrictNormalHom (M.rayClassField Ω)
  let κ : G K Ω →* C := (F.comp (M.rayClassArtinEquiv Ω).symm.toMonoidHom).comp r
  have hker : r.ker ≤ κ.ker := fun σ hσ => by
    change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = 1
    rw [MonoidHom.mem_ker.1 hσ, map_one, map_one]
  refine ⟨κ, ?_, fun w hw A hA => ?_⟩
  · refine Subgroup.isOpen_mono hker ?_
    have : r.ker = (M.rayClassField Ω).fixingSubgroup := IntermediateField.restrictNormalHom_ker _
    rw [this]
    exact IntermediateField.fixingSubgroup_isOpen _
  · obtain ⟨u, hu, hl⟩ := CompanionTheory.FamInh.exists_place_between (L := M.rayClassField Ω) hA
    have hI : u.asIdeal.inertia (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) = ⊥ :=
      (CompanionTheory.FamInh.inertia_eq_bot_iff w u).2 (M.ramificationIdx_rayClassField_eq_one Ω hw u)
    refine ⟨fun σ hσ => hker ?_, fun σ hσ => ?_⟩
    · have := CompanionTheory.FamInh.res_mem_inertia hu hσ
      rw [hI] at this
      exact this
    · haveI : Finite (𝓞 (M.rayClassField Ω) ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
      have e : r σ = M.rayClassArtinEquiv Ω (M.primeClass hw) := by
        rw [M.rayClassArtinEquiv_primeClass Ω hw u]
        exact GroundTheory.Global.IsArithFrobAt.eq_of_inertia_eq_bot (R := 𝓞 K) hI
          (CompanionTheory.FamInh.res_isArithFrobAt hu hσ) (_root_.IsArithFrobAt.arithFrobAt _ _ _)
      change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = _
      rw [e, MulEquiv.symm_apply_apply, hF]
