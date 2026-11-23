import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobson
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

noncomputable section

open IsLocalRing TensorProduct

namespace GlobalTheory.TraitLiftGen

theorem exists_cdvr_of_isRadical {W S : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [CommRing S] (f : W →+* S) {ϖ : W} (hϖ : Irreducible ϖ) (hreg : f ϖ ∈ nonZeroDivisors S)
    (hrad : (Ideal.span {f ϖ}).IsRadical) (hne : Ideal.span {f ϖ} ≠ ⊤) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (h : S →+* W'),
      GlobalTheory.UU.CDVR W' ∧ Irreducible (h (f ϖ)) := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hm.isPrime
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q.IsPrime := hq.1.1
  let T := Localization.AtPrime q
  let t : T := algebraMap S T (f ϖ)
  have hmax : maximalIdeal T = Ideal.span {t} := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes T q _ hq
    rw [← IsLocalization.map_radical q.primeCompl T, hrad.radical, Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_span, Set.image_singleton] at h1
    exact h1.symm
  have htreg : t ∈ nonZeroDivisors T :=
    IsLocalization.nonZeroDivisors_le_comap q.primeCompl T hreg
  have fg : (maximalIdeal T).FG := by rw [hmax]; exact Submodule.fg_span_singleton _
  let V := AdicCompletion (maximalIdeal T) T
  haveI : IsLocalRing V := AdicCompletion.isLocalRing_of_fg fg
  haveI hc : IsAdicComplete (maximalIdeal V) V := AdicCompletion.isAdicComplete_of_fg fg
  have hmV : maximalIdeal V = Ideal.span {algebraMap T V t} := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
    conv_lhs => enter [2]; rw [hmax]
    rw [Ideal.map_span, Set.image_singleton]
  have hn : ¬ IsNilpotent (algebraMap T V t) := by
    rintro ⟨n, hn⟩
    have h1 := congrArg (AdicCompletion.evalₐ (maximalIdeal T) (n + 1)) hn
    rw [← map_pow, AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hmax,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : t ^ n * (1 - t * c) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hc, sub_self]
    have h3 : 1 - t * c = 0 := (mem_nonZeroDivisors_iff_left.mp (pow_mem htreg n)) _ h2
    have h4 : t ∈ maximalIdeal T := hmax ▸ Ideal.mem_span_singleton_self t
    exact (mem_maximalIdeal t).1 h4 (IsUnit.of_mul_eq_one c (sub_eq_zero.mp h3).symm)
  obtain ⟨hd, hdvr, hirr⟩ := GlobalTheory.isDiscreteValuationRing_of_maximalIdeal_eq_span hmV hn
  let h : S →+* V := (algebraMap T V).comp (algebraMap S T)
  have hinj : Function.Injective (h.comp f) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.mp ha with h1 | h1
    · exact (u.isUnit.map _).ne_zero h1
    · exact hirr.ne_zero (IsNilpotent.eq_zero ⟨n, h1⟩)
  exact ⟨V, inferInstance, hd, inferInstance, h, ⟨hdvr, hc, charZero_of_injective_ringHom hinj⟩, hirr⟩

theorem exists_cdvr_of_flat {A R W : Type} [CommRing A] [CommRing R] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [CharZero W] [Algebra A R] [Algebra A W] [Module.Flat A R]
    [IsReduced (ResidueField W ⊗[A] R)] [Nontrivial (ResidueField W ⊗[A] R)] {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W'),
      GlobalTheory.UU.CDVR W' ∧ Irreducible (ι ϖ) ∧ ∀ a, g (algebraMap A R a) = ι (algebraMap A W a) := by
  let S := W ⊗[A] R
  have hreg : algebraMap W S ϖ ∈ nonZeroDivisors S := by
    have hx : IsSMulRegular W ϖ := IsSMulRegular.of_ne_zero hϖ.ne_zero
    have h : IsSMulRegular S (algebraMap W S ϖ) := hx.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hI : (maximalIdeal W).map (algebraMap W S) = Ideal.span {algebraMap W S ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let e : (S ⧸ (maximalIdeal W).map (algebraMap W S)) ≃+* ResidueField W ⊗[A] R :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal W)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A W W (ResidueField W) R).toRingEquiv
  have hrad : (Ideal.span {algebraMap W S ϖ}).IsRadical := by
    rw [← hI, Ideal.isRadical_iff_quotient_reduced]
    exact isReduced_of_injective e e.injective
  have hne : Ideal.span {algebraMap W S ϖ} ≠ ⊤ := by
    rw [← hI, ← Ideal.Quotient.nontrivial_iff]
    exact e.toEquiv.nontrivial
  obtain ⟨W', _, _, _, h, hW', hirr⟩ := exists_cdvr_of_isRadical (algebraMap W S) hϖ hreg hrad hne
  refine ⟨W', inferInstance, inferInstance, inferInstance, h.comp (algebraMap W S),
    h.comp (Algebra.TensorProduct.includeRight (R := A) (A := W) (B := R)).toRingHom, hW', hirr, fun a => ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [← IsScalarTower.algebraMap_apply]

theorem isReduced_completion_tensor_finite (A D : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D] :
    IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] D) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let J := m.map (algebraMap A D)
  haveI : Algebra.EssFiniteType ℤ D := Algebra.EssFiniteType.comp ℤ A D
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D
  haveI : IsReduced (AdicCompletion J D) :=
    GlobalTheory.CompletionReduced.isReduced_adicCompletion D J (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A D)
  have fgm : m.FG := m.fg_of_isNoetherianRing
  haveI : IsAdicComplete (m.map (algebraMap A (AdicCompletion J D))) (AdicCompletion J D) := by
    rw [IsScalarTower.algebraMap_eq A D (AdicCompletion J D), ← Ideal.map_map]
    exact AdicCompletion.isAdicComplete_self J J.fg_of_isNoetherianRing
  obtain ⟨g, hg⟩ := GlobalTheory.exists_adicCompletion_ringHom_extend m (algebraMap A (AdicCompletion J D))
  let g' : AdicCompletion m A →ₐ[A] AdicCompletion J D := { g with commutes' := fun a => RingHom.congr_fun hg a }
  let Φ : AdicCompletion m A ⊗[A] D →ₐ[A] AdicCompletion J D :=
    Algebra.TensorProduct.lift g' (IsScalarTower.toAlgHom A D _) fun _ _ => Commute.all _ _
  have hmap : ∀ {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (u : M →ₗ[A] N) (n : ℕ) (x : M),
      x ∈ (m ^ n • ⊤ : Submodule A M) → u x ∈ (m ^ n • ⊤ : Submodule A N) := by
    intro M N _ _ _ _ u n x hx
    have := Submodule.mem_map_of_mem (f := u) hx
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hdens : ∀ (n : ℕ) (x : AdicCompletion m A ⊗[A] D), ∃ d : D,
      x - 1 ⊗ₜ[A] d ∈ (m ^ n • ⊤ : Submodule A (AdicCompletion m A ⊗[A] D)) := by
    intro n x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨d, hd⟩ := hx
      obtain ⟨d', hd'⟩ := hy
      refine ⟨d + d', ?_⟩
      rw [TensorProduct.tmul_add, add_sub_add_comm]
      exact add_mem hd hd'
    | tmul a d =>
      obtain ⟨a₀, ha₀⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval m A n a)
      have h1 : a - a₀ • (1 : AdicCompletion m A) ∈ (m ^ n • ⊤ : Submodule A (AdicCompletion m A)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval fgm, LinearMap.mem_ker, map_sub, ← ha₀, sub_eq_zero,
          ← Algebra.algebraMap_eq_smul_one]
        rfl
      refine ⟨a₀ • d, ?_⟩
      have := hmap ((TensorProduct.mk A (AdicCompletion m A) D).flip d) n _ h1
      simpa [TensorProduct.sub_tmul, TensorProduct.smul_tmul] using this
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    let e := (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian m D).restrictScalars A
    haveI : IsAdicComplete m (AdicCompletion m D) := AdicCompletion.isAdicComplete fgm
    rw [← e.map_eq_zero_iff]
    refine IsHausdorff.haus' (I := m) _ fun n => ?_
    rw [SModEq.zero]
    refine hmap e.toLinearMap n x ?_
    obtain ⟨d, hd⟩ := hdens n x
    have h1 := hmap Φ.toLinearMap n _ hd
    have h2 : Φ (1 ⊗ₜ[A] d) = algebraMap D _ d := by simp [Φ]
    rw [AlgHom.toLinearMap_apply, map_sub, hx, h2, zero_sub, neg_mem_iff] at h1
    have h3 := hmap ((AdicCompletion.evalₐ J n).restrictScalars A).toLinearMap n _ h1
    have h4 : (m ^ n • ⊤ : Submodule A (D ⧸ J ^ n)) = ⊥ := by
      rw [eq_bot_iff]
      refine Submodule.smul_le.2 fun r hr y _ => ?_
      rw [Submodule.mem_bot, Algebra.smul_def, IsScalarTower.algebraMap_apply A D, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2, zero_mul]
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    rw [h4, Submodule.mem_bot] at h3
    have h5 : d ∈ J ^ n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← (AdicCompletion.evalₐ J n).commutes]
      exact h3
    have h6 : d ∈ (m ^ n • ⊤ : Submodule A D) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
      exact h5
    have h7 := hmap (TensorProduct.mk A (AdicCompletion m A) D 1) n _ h6
    simpa using add_mem hd h7
  exact isReduced_of_injective Φ hinj

theorem isReduced_tensor_of_isIntegralClosure (A C O Ω : Type) [CommRing A] [CommRing C] [Algebra A C] [CommRing O]
    [IsDomain O] [Field Ω] [IsAlgClosed Ω] [Algebra A O] [Algebra O Ω] [Algebra A Ω] [IsScalarTower A O Ω]
    [IsIntegralClosure O A Ω] [IsReduced (O ⊗[A] C)] : IsReduced (Ω ⊗[A] C) := by
  have hinj : Function.Injective (algebraMap O Ω) := IsIntegralClosure.algebraMap_injective O A Ω
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
  let L := FractionRing O
  letI : Algebra L Ω := FractionRing.liftAlgebra O Ω
  haveI : IsScalarTower O L Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  haveI : IsScalarTower A L Ω := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A O L, ← IsScalarTower.algebraMap_apply O L Ω,
      ← IsScalarTower.algebraMap_apply A O Ω]
  haveI h3 : IsReduced (L ⊗[O] (O ⊗[A] C)) :=
    isReduced_of_injective _ (Localization.tensorRightAlgEquiv (nonZeroDivisors O) (O ⊗[A] C)).injective
  haveI h4 : IsReduced (L ⊗[A] C) :=
    isReduced_of_injective _ (Algebra.TensorProduct.cancelBaseChange A O O L C).symm.injective
  haveI : PerfectField L := by
    obtain ⟨p, hp⟩ := ExpChar.exists L
    have hp0 : 0 < p := expChar_pos L p
    haveI : PerfectRing L p := by
      refine PerfectRing.ofSurjective L p fun x => ?_
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
      have hb0 : algebraMap O L b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O Ω (a * b ^ (p - 1))) hp0
      have hzi : IsIntegral A z :=
        IsIntegral.of_pow hp0 (hz ▸ (IsIntegralClosure.isIntegral_iff (A := O)).2 ⟨_, rfl⟩)
      obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := O)).1 hzi
      have hz' : y ^ p = a * b ^ (p - 1) := hinj (by rw [map_pow, hz])
      refine ⟨algebraMap O L y / algebraMap O L b, ?_⟩
      rw [frobenius_def, div_pow, ← map_pow, hz', map_mul, map_pow]
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ', mul_div_mul_right _ _ (pow_ne_zero r hb0)]
    exact PerfectRing.toPerfectField L p
  haveI h5 : IsReduced (Ω ⊗[L] (L ⊗[A] C)) := GlobalTheory.ReducedAlg.isReduced_field_tensor Ω _
  exact isReduced_of_injective _ (Algebra.TensorProduct.cancelBaseChange A L L Ω C).symm.injective

theorem isReduced_field_tensor_completion (A k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [Field k] [Algebra A k] : IsReduced (k ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI : Module.Flat A (AdicCompletion (maximalIdeal A) A) := AdicCompletion.flat_of_isNoetherian _
  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
      IsReduced (Ω ⊗[A] AdicCompletion (maximalIdeal A) A) := by
    intro Ω _ _ _
    have h1 : IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] integralClosure A Ω) := by
      refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
      haveI : Algebra.FiniteType A B := (Subalgebra.fg_iff_finiteType B).mp hB
      haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_injective B.val Subtype.val_injective
      haveI : Module.Finite A B := Algebra.IsIntegral.finite
      exact isReduced_completion_tensor_finite A B
    haveI h2 : IsReduced (integralClosure A Ω ⊗[A] AdicCompletion (maximalIdeal A) A) :=
      isReduced_of_injective _ (Algebra.TensorProduct.comm A _ _).injective
    exact isReduced_tensor_of_isIntegralClosure A _ (integralClosure A Ω) Ω
  haveI := key (AlgebraicClosure k)
  exact isReduced_of_injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A k (AlgebraicClosure k))
      (AlgHom.id A (AdicCompletion (maximalIdeal A) A)))
    (Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap k (AlgebraicClosure k)).injective)

theorem exists_finite_flat_unramified_completion (D E : Type) [CommRing D] [IsLocalRing D] [CommRing E] [IsLocalRing E]
    (h : D →+* E) (hD : IsNoetherianRing D) (hE : IsNoetherianRing E) (hEc : IsAdicComplete (maximalIdeal E) E)
    (het : GlobalTheory.Toroidal.IsEtaleCompletion h) (hfu : ((residue E).comp h).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal D) D →+* E, (∀ a, g (algebraMap D _ a) = h a) ∧ IsLocalHom g ∧ g.Finite ∧
      g.Flat ∧ g.FormallyUnramified := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  haveI := hD; haveI := hE; haveI := hEc
  let A := AdicCompletion (maximalIdeal D) D
  haveI : IsNoetherianRing A := AdicNoeth.isNoetherianRing_adicCompletion D _
  haveI : IsAdicComplete ((maximalIdeal D).map h) E := by rw [hmap]; exact hEc
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal D) h
  letI : Algebra A E := g.toAlgebra
  have hgA : ∀ a, g (algebraMap D A a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal A).map (algebraMap A E) = maximalIdeal E := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal D).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap A E) := ((local_hom_TFAE _).out 0 2).mpr hmA.le

  have hres : ((residue E).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap D A) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite A (E ⧸ (maximalIdeal A).map (algebraMap A E)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap A E)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal A).map (algebraMap A E)) E := by rw [hmA]; infer_instance
  haveI : Module.Finite A E := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

  haveI : Module.Flat A E := by
    refine LocalFlat.flat_of_relationsLift E (I := maximalIdeal A)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    letI : Algebra D E := h.toAlgebra
    haveI : Module.Flat D E := hflat
    have fg := (maximalIdeal D).fg_of_isNoetherianRing
    have hkerA : ∀ x : A, AdicCompletion.evalₐ (maximalIdeal D) n x = 0 ↔ x ∈ maximalIdeal A ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem D,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal A ^ n).map (algebraMap A E) = (maximalIdeal D ^ n).map (algebraMap D E) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal D ^ n).map (g.comp _) = _
      rw [hg]
      rfl
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal D) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal D ^ n).map (algebraMap D E)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal D) n x)
      have hx : x - algebraMap D A a ∈ maximalIdeal A ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap A E x - h a ∈ (maximalIdeal D ^ n).map (algebraMap D E) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap A E x - g (algebraMap D A a) = algebraMap A E (x - algebraMap D A a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E (maximalIdeal D ^ n)).toLinearEquiv

  haveI : Algebra.FormallyUnramified A (ResidueField E) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap A (ResidueField E)).comp (algebraMap D A) = (residue E).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap D A) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified A E := GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  exact ⟨g, hgA, ‹IsLocalHom (algebraMap A E)›, ‹Module.Finite A E›, ‹Module.Flat A E›, ‹Algebra.FormallyUnramified A E›⟩

theorem exists_ringHom_lift {A R W : Type} [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R]
    [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : A →+* R) (ψ : A →+* W) (hR : IsNoetherianRing R)
    (hRc : IsAdicComplete (maximalIdeal R) R) (het : GlobalTheory.Toroidal.IsEtaleCompletion φ)
    (hfu : ((residue R).comp φ).FormallyUnramified) (hW : GlobalTheory.UU.CDVR W) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W'),
      GlobalTheory.UU.CDVR W' ∧ Irreducible (ι ϖ) ∧ ∀ a, g (φ a) = ι (ψ a) := by
  haveI hA : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  obtain ⟨φ', hφ', hloc, hfin, hflat, hur⟩ := exists_finite_flat_unramified_completion A R φ hA hR hRc het hfu
  haveI : IsDiscreteValuationRing W := hW.1
  haveI := hW.2.2
  letI : Algebra A W := ψ.toAlgebra
  haveI : Module.Flat A (AdicCompletion (maximalIdeal A) A) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI := isReduced_field_tensor_completion A (ResidueField W)
  obtain ⟨V, _, _, _, ι₁, g₁, hV, hι₁, hg₁⟩ :=
    exists_cdvr_of_flat (A := A) (R := AdicCompletion (maximalIdeal A) A) hϖ
  haveI : IsLocalRing (AdicCompletion (maximalIdeal A) A) := inferInstance
  have key : ∀ (C : Type) [CommRing C] [IsLocalRing C] (φ' : C →+* R) (g₁ : C →+* V), IsLocalHom φ' → φ'.Finite →
      φ'.Flat → φ'.FormallyUnramified →
      ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : V →+* W') (g : R →+* W'),
        GlobalTheory.UU.CDVR W' ∧ Irreducible (ι (ι₁ ϖ)) ∧ ∀ a, g (φ' a) = ι (g₁ a) := by
    intro C _ _ φ' g₁ hloc hfin hflat hur
    haveI : IsDiscreteValuationRing V := hV.1
    haveI := hV.2.2
    algebraize [φ', g₁]
    haveI : IsLocalHom (algebraMap C R) := hloc
    haveI : Module.FaithfullyFlat C R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    haveI := Algebra.FormallyUnramified.isReduced_of_field (ResidueField V) (ResidueField V ⊗[C] R)
    exact exists_cdvr_of_flat (A := C) (R := R) hι₁
  obtain ⟨W', _, _, _, ι₂, g, hW', hι₂, hg⟩ := key _ φ' g₁ hloc hfin hflat hur
  refine ⟨W', inferInstance, inferInstance, inferInstance, ι₂.comp ι₁, g, hW', hι₂, fun a => ?_⟩
  rw [← hφ', hg, hg₁]
  rfl

end GlobalTheory.TraitLiftGen

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TraitLiftGen

theorem exists_lift_of_specializes : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ hs : χ (closedPoint W) ⤳ ξ (closedPoint R), χ (closedPoint W) ≠ ξ (closedPoint R) → ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) = 1 → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W'), CDvr W' ∧ Irreducible (ι ϖ) ∧ ∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) = ι ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.stalkSpecializes hs).hom a)) := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ hCN hEt hFU W _ _ _ hW ϖ hϖ χ _ hs _ _
  haveI := (GlobalTheory.GModStalk.charZero_essFiniteType_stalk E H D l Xo c Z (ξ (closedPoint R))).2
  exact exists_ringHom_lift (Scheme.stalkClosedPointTo ξ).hom
    ((Scheme.stalkClosedPointTo χ).hom.comp (Z.X.presheaf.stalkSpecializes hs).hom) hCN.1 hCN.2.2.1 hEt hFU hW hϖ

end GlobalTheory.TraitLiftGen
