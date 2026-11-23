import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

theorem hasProjectiveDimensionLT_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1) := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp hM
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hK' := ih K hxK hK
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    exact (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mpr hK'

theorem eq_zero_of_forall_smul_eq_zero_of_free {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {a : R} (h : ∀ m : M, a • m = 0) : a = 0 := by
  let b := Module.Free.chooseBasis R M
  obtain ⟨i⟩ := b.index_nonempty
  have := congrArg b.repr (h (b i))
  rw [map_smul, b.repr_self, map_zero, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_zero] at this
  exact this

theorem free_of_hasProjectiveDimensionLT_of_mul_eq_zero [IsLocalRing R] [IsNoetherianRing R]
    {s : R} (hs : s ≠ 0) (hms : ∀ a ∈ maximalIdeal R, a * s = 0) (k : ℕ) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) : Module.Free R M := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM
    exact Module.free_of_flat_of_isLocalRing
  | succ k ih =>
    classical
    have hfg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
    obtain ⟨t, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
    let π : (t → R) →ₗ[R] M := Fintype.linearCombination R (fun j : t ↦ (j : M))
    have hπ : Function.Surjective π := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hspan]
      exact Submodule.span_mono (fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩)

    have hker : ∀ v ∈ LinearMap.ker π, ∀ i, v i ∈ maximalIdeal R := by
      intro v hv i
      by_contra hvi
      have hu : IsUnit (v i) := (IsLocalRing.notMem_maximalIdeal.mp hvi)
      have hsum : ∑ j, v j • (j : M) = 0 := by
        rw [LinearMap.mem_ker] at hv
        simpa [π, Fintype.linearCombination_apply] using hv
      rw [Fintype.sum_eq_add_sum_compl i] at hsum
      have hmem : (i : M) ∈ Submodule.span R ((t.erase i : Finset M) : Set M) := by
        have h1 : v i • (i : M) = -∑ j ∈ ({i}ᶜ : Finset t), v j • (j : M) :=
          eq_neg_of_add_eq_zero_left hsum
        have h2 : ∑ j ∈ ({i}ᶜ : Finset t), v j • (j : M) ∈
            Submodule.span R ((t.erase i : Finset M) : Set M) := by
          refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          exact ⟨j.2, fun h ↦ hj (Subtype.ext h)⟩
        have h3 : (i : M) = ((hu.unit⁻¹ : Rˣ) : R) • (v i • (i : M)) := by
          rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        have h4 : ((hu.unit⁻¹ : Rˣ) : R) • (v i • (i : M)) ∈
            Submodule.span R ((t.erase i : Finset M) : Set M) := by
          rw [h1]
          exact Submodule.smul_mem _ _ (Submodule.neg_mem _ h2)
        rwa [← h3] at h4
      have htop : Submodule.span R ((t.erase i : Finset M) : Set M) = ⊤ := by
        rw [eq_top_iff, ← hspan, Submodule.span_le]
        intro y hy
        by_cases hyi : y = i
        · rw [hyi]; exact hmem
        · exact Submodule.subset_span (by simp [hyi, hy])
      have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
        (Finset.finite_toSet (t.erase i))
      rw [htop, Set.ncard_coe_finset, Finset.card_erase_of_mem i.2, hcard] at hle
      have hpos : 0 < (⊤ : Submodule R M).spanFinrank := by
        rw [← hcard]; exact Finset.card_pos.mpr ⟨i, i.2⟩
      omega

    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker π)) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp hM
    have hKfree := ih (LinearMap.ker π) hK
    have hKzero : Subsingleton (LinearMap.ker π) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact hs (eq_zero_of_forall_smul_eq_zero_of_free (M := LinearMap.ker π) fun v ↦
        Subtype.ext (funext fun i ↦ by
          simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero,
            Pi.zero_apply]
          rw [mul_comm]; exact hms _ (hker v v.2 i)))
    have hinj : Function.Injective π := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.eq_bot_of_subsingleton
    exact Module.Free.of_equiv (LinearEquiv.ofBijective π ⟨hinj, hπ⟩)

theorem spanFinrank_maximalIdeal_le_quotient_add_one [IsLocalRing R] [IsNoetherianRing R]
    {x : R} [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by
  classical
  obtain ⟨t, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (R ⧸ span {x})).fg_of_isNoetherianRing
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  let S : Finset R := insert x (t.image lift)
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmap : (span ((t.image lift : Finset R) : Set R)).map (Ideal.Quotient.mk (span {x})) =
      maximalIdeal (R ⧸ span {x}) := by
    rw [Ideal.map_span, ← hspan, Finset.coe_image, ← Set.image_comp]
    congr 1
    ext b
    simp [hlift]
  have heq : span (S : Set R) = maximalIdeal R := by
    have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) hmap
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      hcomap] at h2
    rw [Finset.coe_insert, Ideal.span_insert, ← h2, sup_comm]
  have hle : (Ideal.span (S : Set R)).spanFinrank ≤ (S : Set R).ncard :=
    Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet S)
  rw [heq, Set.ncard_coe_finset] at hle
  refine hle.trans ((Finset.card_insert_le _ _).trans ?_)
  rw [← hcard]
  exact Nat.add_le_add_right Finset.card_image_le 1

set_option backward.isDefEq.respectTransparency false in

theorem isRegularLocalRing_of_hasProjectiveDimensionLT [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1)) :
    IsRegularLocalRing R := by
  suffices H : ∀ e : ℕ, ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (n : ℕ),
      HasProjectiveDimensionLT (ModuleCat.of S (S ⧸ maximalIdeal S)) (n + 1) →
      (maximalIdeal S).spanFinrank = e → IsRegularLocalRing S from H _ R n hk rfl
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro S _ _ _ n hk he
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases he0 : e = 0
  · apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [he, he0]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  have hjac : maximalIdeal S ≤ jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hmne : maximalIdeal S ≠ ⊥ := fun h ↦ he0 (by rw [← he, h]; simp)
  by_cases hass : maximalIdeal S ∈ associatedPrimes S S
  ·
    exfalso
    obtain ⟨-, s, hs⟩ := (isAssociatedPrime_iff (I := maximalIdeal S) (M := S)).mp hass
    have hms : ∀ a ∈ maximalIdeal S, a * s = 0 := fun a ha ↦ by
      have := hs ▸ ha
      simpa [Submodule.mem_colon_singleton, smul_eq_mul] using this
    have hs0 : s ≠ 0 := by
      rintro rfl
      have h1 : (1 : S) ∈ maximalIdeal S := by
        rw [hs]; simp [Submodule.mem_colon_singleton]
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hfree := free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs0 hms n
      (S ⧸ maximalIdeal S) hk
    apply hmne
    rw [eq_bot_iff]
    intro a ha
    rw [Submodule.mem_bot]
    exact eq_zero_of_forall_smul_eq_zero_of_free (M := S ⧸ maximalIdeal S) fun y ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact (maximalIdeal S).mul_mem_right y ha

  have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
    intro hle
    exact hmne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
      (by simpa [pow_two, smul_eq_mul] using hle) hjac)
  classical
  have hfin := associatedPrimes.finite S S
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
      x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
    by_contra! hcon
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
      (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h h1
        · exact ((Set.Finite.mem_toFinset _).mp h).isPrime)).mp hcon
    rcases Finset.mem_insert.mp hi with h | h
    · exact hsq (h ▸ hle)
    · have hP := (Set.Finite.mem_toFinset _).mp h
      have : i = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.isPrime.ne_top) hle
      exact hass (this ▸ hP)
  simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
    Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
  obtain ⟨hx2, hxP⟩ := hxn
  have hxreg : IsSMulRegular S x := by
    have : x ∉ ⋃ p ∈ associatedPrimes S S, (p : Set S) := by
      simp only [Set.mem_iUnion, not_exists]
      exact fun p hp hxp ↦ hxP p hp hxp
    rw [biUnion_associatedPrimes_eq_compl_regular S S] at this
    simpa using this

  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let T := ModuleCat.shortComplexOfCompEqZero (maximalIdeal S).subtype (maximalIdeal S).mkQ
    (LinearMap.exact_subtype_mkQ _).linearMap_comp_eq_zero
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_subtype_mkQ _) (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
  have : HasProjectiveDimensionLT T.X₃ (n + 1) := hk
  have hk2 : HasProjectiveDimensionLT T.X₃ (n + 2) :=
    hasProjectiveDimensionLT_of_ge T.X₃ (n + 1) (n + 2) (by omega)
  have hproj : Projective T.X₂ := by
    rw [← IsProjective.iff_projective]; infer_instance
  have hm : HasProjectiveDimensionLT (ModuleCat.of S (maximalIdeal S)) (n + 1) :=
    (hT.hasProjectiveDimensionLT_X₃_iff n hproj).mp hk2
  have hxm : IsSMulRegular (maximalIdeal S) x :=
    fun a b h ↦ Subtype.ext (hxreg (congrArg Subtype.val h))
  have hB := hasProjectiveDimensionLT_quotSMulTop hxreg n (maximalIdeal S) hxm hm

  let x' : maximalIdeal S := ⟨x, hx⟩
  let ι₀ : (S ⧸ span {x}) →ₗ[S ⧸ span {x}] QuotSMulTop x (maximalIdeal S) :=
    LinearMap.toSpanSingleton (S ⧸ span {x}) _ (Submodule.mkQ _ x')
  have hι : maximalIdeal (S ⧸ span {x}) ≤ LinearMap.ker ι₀ := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : a ∈ maximalIdeal S := by
      rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk (span {x}))]; exact hb
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      show Ideal.Quotient.mk (span {x}) a = algebraMap S (S ⧸ span {x}) a from rfl,
      algebraMap_smul, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨a, ha⟩, Submodule.mem_top, Subtype.ext (mul_comm x a)⟩
  let ι := (maximalIdeal (S ⧸ span {x})).liftQ ι₀ hι
  let v0 := (maximalIdeal S).toCotangent x'
  have hv0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ResidueField S) hv0
  let q : (S ⧸ maximalIdeal S) →ₐ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    Ideal.quotientMapₐ (maximalIdeal (S ⧸ span {x})) (Ideal.Quotient.mkₐ S (span {x})) (by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.mem_comap,
        IsLocalRing.maximalIdeal_comap]
      exact ha)
  let φ : maximalIdeal S →ₗ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    q.toLinearMap ∘ₗ (f.restrictScalars S) ∘ₗ (maximalIdeal S).toCotangent
  have hxq : algebraMap S ((S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x})) x = 0 := by
    rw [IsScalarTower.algebraMap_apply S (S ⧸ span {x}),
      show algebraMap S (S ⧸ span {x}) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x), map_zero]
  have hφ : x • (⊤ : Submodule S (maximalIdeal S)) ≤ LinearMap.ker φ := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, hxq, zero_mul]
  let ρ₀ : QuotSMulTop x (maximalIdeal S) →ₗ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    (x • (⊤ : Submodule S (maximalIdeal S))).liftQ φ hφ
  let ρ := ρ₀.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
  have hρι : ρ ∘ₗ ι = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext_ring
    have h1 : f v0 = 1 := hf
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, ι, Submodule.liftQ_apply, ι₀,
      LinearMap.toSpanSingleton_apply, one_smul, ρ, LinearMap.extendScalarsOfSurjective_apply,
      ρ₀, φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    change q (f v0) = _
    rw [h1, map_one]
    rfl
  let rt : Retract (ModuleCat.of (S ⧸ span {x}) ((S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x})))
      (ModuleCat.of (S ⧸ span {x}) (QuotSMulTop x (maximalIdeal S))) :=
    { i := ModuleCat.ofHom ι
      r := ModuleCat.ofHom ρ
      retract := by rw [← ModuleCat.ofHom_comp, hρι, ModuleCat.ofHom_id] }
  have hkB := rt.hasProjectiveDimensionLT (n + 1)
  have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hregB := ih _ (by omega) (S ⧸ span {x}) n hkB rfl
  have hdimB := (isRegularLocalRing_iff (S ⧸ span {x})).mp hregB
  have hdim : ringKrullDim (S ⧸ span {x}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hx
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := spanFinrank_maximalIdeal_le_quotient_add_one (R := S) (x := x)
  rw [← hdim, ← hdimB]
  exact_mod_cast h1

theorem IsRegularLocalRing.localization_atPrime [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R = d :=
    ⟨_, ((isRegularLocalRing_iff R).mp inferInstance).symm⟩
  have h1 := hasProjectiveDimensionLT_of_isRegularLocalRing hd (R ⧸ p)
  have h2 : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl) d :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE d p.primeCompl _
  let Rp := Localization.AtPrime p
  let f := Algebra.linearMap R Rp
  let g := (p : Submodule R R).toLocalizedQuotient' Rp p.primeCompl f
  have hl : (p : Submodule R R).localized' Rp p.primeCompl f = maximalIdeal Rp := by
    rw [Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal]
  let e : (Rp ⧸ (p : Submodule R R).localized' Rp p.primeCompl f) ≃ₗ[Rp] Rp ⧸ maximalIdeal Rp :=
    Submodule.quotEquivOfEq _ _ hl
  let g' := (e.restrictScalars R).toLinearMap ∘ₗ g
  have : IsLocalizedModule p.primeCompl g' := IsLocalizedModule.of_linearEquiv _ _ _
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (R ⧸ p)) p.primeCompl
  let e' := (IsLocalizedModule.linearEquiv p.primeCompl
    ((ModuleCat.of R (R ⧸ p)).localizedModuleMkLinearMap p.primeCompl) g').extendScalarsOfIsLocalization
    p.primeCompl Rp
  have h3 : HasProjectiveDimensionLT (ModuleCat.of Rp (Rp ⧸ maximalIdeal Rp)) (d + 1) :=
    hasProjectiveDimensionLT_of_iso e'.toModuleIso (d + 1)
  exact isRegularLocalRing_of_hasProjectiveDimensionLT d h3

end GroundTheory.Arith.SchemeCoh
