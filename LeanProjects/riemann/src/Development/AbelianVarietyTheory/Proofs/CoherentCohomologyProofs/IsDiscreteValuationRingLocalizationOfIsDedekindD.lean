import Mathlib

namespace GlobalTheory

open IsDiscreteValuationRing IsLocalRing Module TensorProduct

namespace NormVal

section Det

variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

lemma length_quot_span_singleton (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := Ring.ord_eq_addVal a

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

lemma addVal_det_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  classical
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have hfe : f = N.subtype.comp (e : M →ₗ[R] N) := by ext x; rfl
  have hass : Associated (LinearMap.det f) (LinearMap.det g) := by
    rw [hfe]; exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, g (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : N) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hg : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  rw [(addVal_eq_iff_associated _ _).2 hass, ← LinearMap.det_toMatrix b', hg, Matrix.det_diagonal,
    addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => (length_quot_span_singleton _).symm

lemma length_quot_range_of_not_injective (f : M →ₗ[R] M) (hf : ¬ Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq] at h1
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h3 : 0 < Module.finrank R (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
    exact hf
  have h4 : 0 < Module.finrank R (M ⧸ LinearMap.range f) := by omega
  obtain ⟨v, hv⟩ : ∃ v : M ⧸ LinearMap.range f, ∀ a : R, a • v = 0 → a = 0 := by
    by_contra hcon
    push Not at hcon
    have : Module.finrank R (M ⧸ LinearMap.range f) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro v
      obtain ⟨a, ha, ha0⟩ := hcon v
      exact ⟨a, ha0, ha⟩
    omega
  have hinj : Function.Injective (LinearMap.toSpanSingleton R _ v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hv a ha
  have h5 := Module.length_le_of_injective _ hinj
  have h6 : Module.length R R = ⊤ := by
    rw [← Ring.ord_zero, Ring.ord_eq_addVal, addVal_zero]
  rwa [h6, top_le_iff] at h5

lemma addVal_det (f : M →ₗ[R] M) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  by_cases hf : Function.Injective f
  · exact addVal_det_of_injective f hf
  · rw [length_quot_range_of_not_injective f hf, addVal_eq_top_iff,
      LinearMap.det_eq_zero_iff_ker_ne_bot, Ne, LinearMap.ker_eq_bot]
    exact hf

end Det

section Semilocal

variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

lemma liesOver_maximalIdeal (n : Ideal S) [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).symm⟩

lemma length_quot_maximal (n : Ideal S) [n.IsMaximal] :
    Module.length R (S ⧸ n) = n.inertiaDeg R := by
  have := liesOver_maximalIdeal R n
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) n]
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n) := Module.Finite.of_restrictScalars_finite R _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

lemma isLocalHom_algebraMap (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B] [IsScalarTower R S B] :
    IsLocalHom (algebraMap R B) := by
  have := liesOver_maximalIdeal R n
  refine ⟨fun a ha => ?_⟩
  rw [IsScalarTower.algebraMap_apply R S B, IsLocalization.AtPrime.isUnit_to_map_iff B n] at ha
  by_contra hu
  exact ha ((Ideal.mem_of_liesOver n (maximalIdeal R) a).1 hu)

lemma inertiaDeg_eq_finrank_residueField (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B]
    [IsLocalRing B] [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B]
    [IsScalarTower R S B] [IsLocalHom (algebraMap R B)] :
    n.inertiaDeg R = Module.finrank (ResidueField R) (ResidueField B) := by
  have := liesOver_maximalIdeal R n
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) n]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal n B) ?_
  ext a
  change residue B (algebraMap R B a) =
    IsLocalization.AtPrime.equivQuotMaximalIdeal n B (Ideal.Quotient.mk n (algebraMap R S a))
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← IsScalarTower.algebraMap_apply]
  rfl

lemma finite_residueField (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B]
    [IsLocalRing B] [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B]
    [IsScalarTower R S B] [IsLocalHom (algebraMap R B)] :
    Module.Finite (ResidueField R) (ResidueField B) :=
  Module.finite_of_finrank_pos <| by
    rw [← inertiaDeg_eq_finrank_residueField R n B]
    exact Ideal.inertiaDeg_pos n R

include R in

lemma finite_maximalSpectrum : Finite (MaximalSpectrum S) := by
  have := Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (maximalIdeal R)
  have := this.to_subtype
  refine Finite.of_injective (fun n : MaximalSpectrum S =>
    (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal R n.asIdeal⟩ :
      (maximalIdeal R).primesOver S)) ?_
  intro a b h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)

lemma length_localization_quot_maximal (m n : MaximalSpectrum S) [Decidable (n = m)]
    (B : Type*) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B n.asIdeal] :
    Module.length B (B ⧸ m.asIdeal.map (algebraMap S B)) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h
    have := IsLocalization.AtPrime.isLocalRing B n.asIdeal
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal n.asIdeal B, Module.length_eq_one_iff,
      isSimpleModule_iff_isCoatom]
    exact Ideal.isMaximal_def.1 inferInstance
  · rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
    have : ¬ m.asIdeal ≤ n.asIdeal := fun hle =>
      h (MaximalSpectrum.ext (m.isMaximal.eq_of_le n.isMaximal.ne_top hle).symm)
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 this
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hy)
      (IsLocalization.map_units _ (⟨y, hyn⟩ : n.asIdeal.primeCompl))

variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

lemma length_eq_sum_tensor {X : Type*} [AddCommGroup X] [Module S X] (hX : IsFiniteLength S X) :
    ∀ [Module R X] [IsScalarTower R S X], Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (A n ⊗[S] X) * n.asIdeal.inertiaDeg R := by
  classical
  induction hX with
  | of_subsingleton => intro _ _; simp
  | @of_simple_quotient X _ _ N hs _ ih =>
    intro _ _
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    let f : N →ₗ[S] X := N.subtype
    let g : X →ₗ[S] S ⧸ m := e.toLinearMap.comp N.mkQ
    have hf : Function.Injective f := N.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp N.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by simp [f, g])
    rw [length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg, ih,
      length_quot_maximal]
    have key : ∀ n : MaximalSpectrum S,
        Module.length (A n) (A n ⊗[S] X) =
        Module.length (A n) (A n ⊗[S] N) + if n = ⟨m, hm⟩ then 1 else 0 := by
      intro n
      have : Module.Flat S (A n) := IsLocalization.flat (A n) n.asIdeal.primeCompl
      rw [length_eq_add_of_exact (AlgebraTensorModule.lTensor (A n) (A n) f)
        (AlgebraTensorModule.lTensor (A n) (A n) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (A n) hg) (Module.Flat.lTensor_exact (A n) hfg),
        ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) m).toLinearEquiv.length_eq,
        ← length_localization_quot_maximal ⟨m, hm⟩ n (A n)]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    simp

lemma length_quot_eq_sum (I : Ideal S) (hI : Module.length R (S ⧸ I) ≠ ⊤) :
    Module.length R (S ⧸ I) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ I.map (algebraMap S (A n))) * n.asIdeal.inertiaDeg R := by
  have h : IsFiniteLength S (S ⧸ I) := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hI
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hI.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [length_eq_sum_tensor R A h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A n) I).toLinearEquiv.length_eq]

end Semilocal

end NormVal

open NormVal

variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

theorem addVal_norm_eq_length (x : S) :
    addVal R (Algebra.norm R x) = Module.length R (S ⧸ Ideal.span {x}) := by
  rw [Algebra.norm_apply, addVal_det]
  have h : LinearMap.range (Algebra.lmul R S x) = (Ideal.span {x}).restrictScalars R := by
    ext y
    simp [Ideal.mem_span_singleton', mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ h).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {x})).length_eq]

theorem addVal_norm_ne_top_iff (x : S) :
    addVal R (Algebra.norm R x) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [Ne, addVal_eq_top_iff, Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot', mem_nonZeroDivisors_iff_left]
  simp

theorem length_quot_span_ne_top_iff (x : S) :
    Module.length R (S ⧸ Ideal.span {x}) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [← addVal_norm_eq_length, addVal_norm_ne_top_iff]

section Local

variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

theorem addVal_norm_eq_sum_length {x : S} (hx : x ∈ nonZeroDivisors S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ Ideal.span {algebraMap S (A n) x}) * n.asIdeal.inertiaDeg R := by
  rw [addVal_norm_eq_length, length_quot_eq_sum R A _ ((length_quot_span_ne_top_iff R x).2 hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Ideal.map_span, Set.image_singleton]

variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]

theorem addVal_norm_eq_sum (x : S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      addVal (A n) (algebraMap S (A n) x) * n.asIdeal.inertiaDeg R := by
  by_cases hx : x ∈ nonZeroDivisors S
  · rw [addVal_norm_eq_sum_length R A hx]
    exact Finset.sum_congr rfl fun n _ => by rw [length_quot_span_singleton]
  · have h1 : addVal R (Algebra.norm R x) = ⊤ := by
      rwa [← addVal_norm_ne_top_iff R, not_not] at hx
    rw [mem_nonZeroDivisors_iff_left] at hx
    push Not at hx
    obtain ⟨y, hxy, hy⟩ := hx
    have hne : LinearMap.ker (LinearMap.toSpanSingleton S S y) ≠ ⊤ := by
      intro h
      have : (1 : S) ∈ LinearMap.ker (LinearMap.toSpanSingleton S S y) := h ▸ Submodule.mem_top
      exact hy (by simpa using this)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let n : MaximalSpectrum S := ⟨m, hm⟩
    have hy' : algebraMap S (A n) y ≠ 0 := by
      intro h
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.asIdeal.primeCompl (A n) y).1 h
      exact s.2 (hle (by simpa using hs))
    have hx' : algebraMap S (A n) x = 0 := by
      have := congrArg (algebraMap S (A n)) hxy
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hy'
    rw [h1, eq_comm, ENat.sum_eq_top]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    rw [hx', addVal_zero, ENat.top_mul]
    exact_mod_cast (Ideal.inertiaDeg_pos n.asIdeal R).ne'

include R in

theorem addVal_localization_ne_top {x : S} (hx : x ∈ nonZeroDivisors S) (n : MaximalSpectrum S) :
    addVal (A n) (algebraMap S (A n) x) ≠ ⊤ := by
  intro h
  refine (addVal_norm_ne_top_iff R x).2 hx ?_
  rw [addVal_norm_eq_sum R A, ENat.sum_eq_top]
  refine ⟨n, Finset.mem_univ _, ?_⟩
  rw [h, ENat.top_mul]
  exact_mod_cast (Ideal.inertiaDeg_pos n.asIdeal R).ne'

variable [∀ n, Algebra R (A n)] [∀ n, IsScalarTower R S (A n)]
  [∀ n, IsLocalHom (algebraMap R (A n))]

end Local

include R in

theorem isDiscreteValuationRing_localization_of_isDedekindDomain [IsDedekindDomain S]
    (n : MaximalSpectrum S) : IsDiscreteValuationRing (Localization.AtPrime n.asIdeal) := by
  have := liesOver_maximalIdeal R n.asIdeal
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) n.asIdeal) _

end GlobalTheory
