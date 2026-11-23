import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing UpperTheory.V.Alg

open private UpperTheory.V.Pr.npe_dim_one from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

private theorem fc_abs (D V : Type) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] [Finite (ResidueField D)] [Ring.DimensionLEOne D]
    [CommRing V] [IsDomain V] [ValuationRing V] [Algebra D V] [FaithfulSMul D V] [IsLocalHom (algebraMap D V)]
    (hm : maximalIdeal D ≠ ⊥)
    (hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b) :
    IsDiscreteValuationRing V ∧ IsAdicComplete (maximalIdeal V) V ∧ Finite (ResidueField V) := by
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki_of_birational (A := D) (B := V) hB).1
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle : (maximalIdeal D).map (algebraMap D V) ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit (algebraMap D V) a ha
  have h1 := GlobalTheory.finite_quotient_span_of_birational hB ht0
  have hs : Ideal.span {algebraMap D V t} ≤ (maximalIdeal D).map (algebraMap D V) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ ht)
  have h2 : Module.Finite D (V ⧸ (maximalIdeal D).map (algebraMap D V)) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ D hs).toLinearMap
      (Ideal.Quotient.factor_surjective hs)
  have h3 : IsHausdorff ((maximalIdeal D).map (algebraMap D V)) V :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal V).ne_top hle)
  have h4 : Module.Finite D V := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    have := hle (Ideal.mem_map_of_mem _ ht)
    rw [h, Ideal.mem_bot] at this
    exact ht0 (FaithfulSMul.algebraMap_injective D V (this.trans (map_zero _).symm))
  have hval : ValuationRing V := inferInstance
  refine ⟨((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval,
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite D V, ?_⟩
  have : Module.Finite (ResidueField D) (ResidueField V) := inferInstance
  exact Module.finite_of_finite (ResidueField D)

private theorem fc_point (D : Type) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] [Finite (ResidueField D)] (hd : ringKrullDim D = 1) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A),
      IsAdicComplete (maximalIdeal A) A ∧ Finite (ResidueField A) ∧
        ∃ φ : D →+* A, Function.Injective φ ∧ IsLocalHom φ := by
  have hk : Ring.KrullDimLE 1 D := by
    rw [Ring.krullDimLE_iff, hd]; exact le_rfl
  have : Ring.DimensionLEOne D :=
    ⟨fun {q} hq hq' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hk q hq hq'⟩
  have hm : maximalIdeal D ≠ ⊥ := fun h => by
    rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.2 h)] at hd
    exact absurd hd (by decide)
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap D (FractionRing D))
  let φ : D →+* V := (algebraMap D (FractionRing D)).codRestrict V.toSubring hV
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val h)
  letI : Algebra D V := φ.toAlgebra
  have : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ
  have hl : IsLocalHom (algebraMap D V) := hloc
  obtain ⟨h1, h2, h3⟩ := fc_abs D V hm fun x => by
    obtain ⟨⟨b, c⟩, h⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ((mul_comm _ _).trans h)⟩
  exact ⟨V, inferInstance, inferInstance, h1, h2, h3, φ, hφ, hl⟩

private theorem fc_finres (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R]
    [Algebra O R] [IsCO O R] : Finite (ResidueField R) :=
  Finite.of_surjective _ (resMap_bijective O R).2

private theorem fc_sign {σ : Type} (wt : σ → ℤ) (n : σ →₀ ℕ) (hn : n ≠ 0) (hw : Finsupp.weight wt n = 0)
    (P : σ → Prop) (h0 : ∀ i, wt i = 0 → P i) (h : (∀ i, wt i < 0 → P i) ∨ ∀ i, 0 < wt i → P i) :
    ∃ i ∈ n.support, P i := by
  by_contra hc
  push Not at hc
  have hne := Finsupp.support_nonempty_iff.2 hn
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rcases h with h | h
  · refine absurd hw (ne_of_gt (Finset.sum_pos (fun i hi => ?_) hne))
    have h1 : 0 < wt i := by
      rcases lt_trichotomy (wt i) 0 with e | e | e
      · exact absurd (h i e) (hc i hi)
      · exact absurd (h0 i e) (hc i hi)
      · exact e
    have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)
    rw [nsmul_eq_mul]
    positivity
  · refine absurd hw (ne_of_lt (Finset.sum_neg (fun i hi => ?_) hne))
    have h1 : wt i < 0 := by
      rcases lt_trichotomy (wt i) 0 with e | e | e
      · exact e
      · exact absurd (h0 i e) (hc i hi)
      · exact absurd (h i e) (hc i hi)
    have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)
    rw [nsmul_eq_mul]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast this) h1

private theorem fc_contract {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ϖ : O)
    (b : W.gr 0) (hb : ((b : W.A) : R) ∈ Ideal.span {algebraMap O R ϖ}) :
    b ∈ Ideal.span {algebraMap O (W.gr 0) ϖ} := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  obtain ⟨g, rfl⟩ := W.surj r
  obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
  have hfb' : W.π f = ((b : W.A) : R) := hfb
  have h1 : ϖ • g - f ∈ RingHom.ker W.π := by
    rw [RingHom.mem_ker, map_sub, map_smul, hfb', ← hr, Algebra.smul_def, mul_comm, sub_self]
  have h2 := W.homog _ h1 0
  have h3 : wcomp O W.wt 0 f = f := by
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  rw [map_sub, map_smul, h3, RingHom.mem_ker, map_sub, map_smul, hfb', sub_eq_zero] at h2
  have hp : W.π (wcomp O W.wt 0 g) ∈ W.part 0 := ⟨_, wcomp_mem O W.wt 0 g, rfl⟩
  refine Ideal.mem_span_singleton'.2 ⟨⟨⟨_, W.part_le_A hp⟩, hp⟩, Subtype.ext (Subtype.ext ?_)⟩
  rw [← h2, Algebra.smul_def, mul_comm]
  rfl

theorem UpperTheory.V.Pr.finCrit :
    UpperTheory.V.Pr.FinCrit := by
  intro O R _ _ _ _ _ _ _ _ W hz H
  classical
  haveI hB : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz
  obtain ⟨h1, u, hu, hmax⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials O ℤ R W hz
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO := hϖ.maximalIdeal_eq
  have hJ : (maximalIdeal O).map (algebraMap O (W.gr 0)) = Ideal.span {algebraMap O (W.gr 0) ϖ} := by
    rw [hmO, Ideal.map_span, Set.image_singleton]
  have hrad : ∀ b ∈ u, ((b : W.A) : R) ∈ (Ideal.span {algebraMap O R ϖ}).radical := by
    intro b hb
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    by_contra hbQ
    have hbm : ((b : W.A) : R) ∈ maximalIdeal R :=
      (h1 b).1 (hmax ▸ Ideal.mem_sup_right (Ideal.subset_span hb))
    obtain ⟨p, hp, hQle, hbp, hd⟩ := UpperTheory.V.Pr.npe_dim_one Q hbm hbQ
    haveI : IsCO O (R ⧸ p) := UpperTheory.V.Alg.co_quot O R (R ⧸ p) (Ideal.Quotient.mkₐ O p)
      Ideal.Quotient.mk_surjective
    haveI := fc_finres O (R ⧸ p)
    obtain ⟨A, _, _, _, hc, hf, φ, hφ, hl⟩ := fc_point (R ⧸ p) hd
    letI : Algebra O A := (φ.comp (algebraMap O (R ⧸ p))).toAlgebra
    haveI : UpperTheory.V.Pr.IsCD O A :=
      { complete := hc
        isLocalHom := inferInstanceAs (IsLocalHom (φ.comp (algebraMap O (R ⧸ p))))
        fin := hf }
    let f : R →ₐ[O] A := { φ.comp (Ideal.Quotient.mk p) with commutes' := fun _ => rfl }
    have hker : ∀ x, f x = 0 ↔ x ∈ p := fun x => by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff φ hφ]
      rfl
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    have hfl : IsLocalHom f := ⟨fun a ha =>
      IsLocalHom.map_nonunit (f := φ.comp (Ideal.Quotient.mk p)) a ha⟩
    obtain ⟨h0, hs⟩ := H A f hfl fun a ha => by
      rw [← f.commutes, hker]
      rw [hmO] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      exact p.mul_mem_left _ (hQle (hQ (Ideal.mem_span_singleton_self _)))
    obtain ⟨n, hn, hw, hbn⟩ := hu b hb
    obtain ⟨i, hi, hi0⟩ := fc_sign W.wt n hn hw _ h0 hs
    apply hbp
    rw [hbn]
    exact Ideal.prod_mem _ hi (Ideal.pow_mem_of_mem _ ((hker _).1 hi0) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)))
  have hrad' : maximalIdeal (W.gr 0) ≤ ((maximalIdeal O).map (algebraMap O (W.gr 0))).radical := by
    rw [hmax]
    refine sup_le Ideal.le_radical (Ideal.span_le.2 fun b hb => ?_)
    obtain ⟨N, hN⟩ := hrad b hb
    exact ⟨N, hJ ▸ fc_contract W ϖ (b ^ N) hN⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad' (IsNoetherian.noetherian _)
  haveI : Finite (W.gr 0 ⧸ maximalIdeal (W.gr 0)) := fc_finres O (W.gr 0)
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal (W.gr 0))) N
  haveI : Finite (W.gr 0 ⧸ (maximalIdeal O).map (algebraMap O (W.gr 0))) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hN)
  haveI : IsHausdorff ((maximalIdeal O).map (algebraMap O (W.gr 0))) (W.gr 0) :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal (W.gr 0)).ne_top
      (le_sup_left.trans hmax.ge))
  haveI : Module.Finite O (W.gr 0) := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal O)
  let e : W.gr 0 →ₗ[O] W.part 0 :=
    { toFun := fun b => ⟨((b : W.A) : R), b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e fun x => ⟨⟨⟨x.1, W.part_le_A x.2⟩, x.2⟩, rfl⟩
