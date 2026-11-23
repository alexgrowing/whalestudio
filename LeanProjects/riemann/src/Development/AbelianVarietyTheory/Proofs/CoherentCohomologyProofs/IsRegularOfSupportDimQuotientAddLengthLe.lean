import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsRegularQuotSMulTop

open RingTheory.Sequence IsLocalRing TensorProduct

namespace GlobalTheory

section Flat

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem IsQuasiRegularSeq.mem_pow_smul_of_map_mem {ι : Type*} [Finite ι] {f : ι → A}
    (h : IsQuasiRegularSeq M f) {F : Type*} [AddCommGroup F] [Module A F] (g : F →ₗ[A] M)
    (hg : ∀ z, g z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A M) →
      z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A F)) (n : ℕ) (z : F)
    (hz : g z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A M)) :
    z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f n z).mp (ih (powGr.pow_succ_smul_le _ M n hz))
    refine sum_monoVal_smul_mem_pow_succ f fun α => hg _ ?_
    exact h n (fun α => g (c α)) (by simpa using hz) α

theorem sup_pow_smul_top_eq_top {I : Ideal A} {N : Submodule A M} (h : N ⊔ I • ⊤ = ⊤) (n : ℕ) :
    N ⊔ I ^ n • ⊤ = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine eq_top_iff.mpr (ih.ge.trans (sup_le le_sup_left ?_))
    refine (Submodule.smul_mono le_rfl h.ge).trans ?_
    rw [Submodule.smul_sup, ← mul_smul, ← pow_succ]
    exact sup_le_sup_right Submodule.smul_le_right _

theorem flat_of_basis_mod_pow [IsNoetherianRing A] (B : Type*) [CommRing B] [IsNoetherianRing B]
    [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) {S : Type*} (m : S → M)
    (hsurj : Submodule.span A (Set.range m) ⊔ I • ⊤ = ⊤)
    (hinj : ∀ (n : ℕ) (z : S →₀ A),
      Finsupp.linearCombination A m z ∈ (I ^ n • ⊤ : Submodule A M) → ∀ s, z s ∈ I ^ n) :
    Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  haveI : SMulCommClass A B M := IsScalarTower.to_smulCommClass
  haveI : Module.Finite B (M ⊗[A] J) := by
    exact Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M J)
  let φ : (S →₀ J) →ₗ[A] M ⊗[A] J := Finsupp.lsum A fun s => TensorProduct.mk A M J (m s)
  have hφ : LinearMap.range φ ⊔ I • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    induction t with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul y j =>
      have hy : y ∈ Submodule.span A (Set.range m) ⊔ I • ⊤ := by rw [hsurj]; trivial
      have := Submodule.mem_map_of_mem (f := (TensorProduct.mk A M J).flip j) hy
      rw [Submodule.map_sup, Submodule.map_smul''] at this
      refine SetLike.le_def.mp (sup_le_sup ?_ (Submodule.smul_mono le_rfl le_top)) this
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨Finsupp.single s j, by simp [φ]⟩
  let μ : M ⊗[A] J →ₗ[A] M := (TensorProduct.rid A M).toLinearMap ∘ₗ J.subtype.lTensor M
  have hμφ : ∀ w, μ (φ w) =
      Finsupp.linearCombination A m (Finsupp.mapRange.linearMap J.subtype w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single s j => simp [μ, φ]
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (M := A) J
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hμt : μ t = 0 := by simp [μ, ht]
  have key : ∀ n : ℕ, t ∈ (I ^ n • ⊤ : Submodule A (M ⊗[A] J)) := by
    intro n
    have h1 : t ∈ LinearMap.range φ ⊔ I ^ (n + c) • ⊤ := by
      rw [sup_pow_smul_top_eq_top hφ]; trivial
    obtain ⟨_, ⟨w, rfl⟩, v, hv, rfl⟩ := Submodule.mem_sup.mp h1
    refine add_mem ?_ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hv)
    have h2 : μ (φ w) ∈ (I ^ (n + c) • ⊤ : Submodule A M) := by
      rw [map_add, add_eq_zero_iff_eq_neg] at hμt
      rw [hμt, neg_mem_iff]
      have := Submodule.mem_map_of_mem (f := μ) hv
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    rw [hμφ] at h2
    have h3 : ∀ s, w s ∈ (I ^ n • ⊤ : Submodule A J) := by
      intro s
      have h4 : (w s : A) ∈ (I ^ (n + c) • ⊤ ⊓ J : Submodule A A) :=
        ⟨by simpa using hinj _ _ h2 s, (w s).2⟩
      rw [hc _ (by omega), Nat.add_sub_cancel] at h4
      rw [Submodule.mem_smul_top_iff]
      exact Submodule.smul_mono le_rfl inf_le_right h4
    rw [show φ w = w.sum fun s j => m s ⊗ₜ j from rfl]
    refine Submodule.sum_mem _ fun s _ => ?_
    have := Submodule.mem_map_of_mem (f := TensorProduct.mk A M J (m s)) (h3 s)
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have h0 := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[A] J) _ hI
  rw [← Submodule.mem_bot B, ← h0, Submodule.mem_iInf]
  intro n
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars]
  exact key n

theorem IsQuasiRegularSeq.flat_of_isMaximal [IsNoetherianRing A] (B : Type*) [CommRing B]
    [IsNoetherianRing B] [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {ι : Type*} [Finite ι] {f : ι → A} (h : IsQuasiRegularSeq M f)
    (hmax : (Ideal.span (Set.range f)).IsMaximal)
    (hI : (Ideal.span (Set.range f)).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) :
    Module.Flat A M := by
  set I := Ideal.span (Set.range f) with hIdef
  letI := Ideal.Quotient.field I
  let b := Module.Free.chooseBasis (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))
  choose m hm using fun s => Submodule.Quotient.mk_surjective _ (b s)
  have hb : ∀ z, (Submodule.Quotient.mk (Finsupp.linearCombination A m z) :
      M ⧸ (I • ⊤ : Submodule A M)) =
      Finsupp.linearCombination (A ⧸ I) b (z.mapRange (Ideal.Quotient.mk I) (map_zero _)) := by
    intro z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, Submodule.Quotient.mk_add, hx, hy, Finsupp.mapRange_add (map_add _), map_add]
    | single s a => simp [hm, ← Ideal.Quotient.algebraMap_eq]
  refine flat_of_basis_mod_pow B hI m ?_ fun n z hz s => ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨z, hz⟩ := Finsupp.mapRange_surjective (Ideal.Quotient.mk I) (map_zero _)
      Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk y))
    have h1 := hb z
    rw [hz, b.linearCombination_repr, Submodule.Quotient.eq'] at h1
    have h2 : Finsupp.linearCombination A m z ∈ Submodule.span A (Set.range m) := by
      rw [← Finsupp.range_linearCombination]
      exact ⟨z, rfl⟩
    simpa using Submodule.add_mem_sup h2 h1
  · have h1 := h.mem_pow_smul_of_map_mem (Finsupp.linearCombination A m) (fun z hz => ?_) n z hz
    · have := Submodule.mem_map_of_mem (f := Finsupp.lapply (R := A) s) h1
      rw [Submodule.map_smul''] at this
      simpa using Submodule.smul_mono le_rfl le_top this
    · rw [← Submodule.Quotient.mk_eq_zero, hb] at hz
      have h2 := (linearIndependent_iff.mp b.linearIndependent) _ hz
      rw [← z.sum_single]
      refine Submodule.sum_mem _ fun s _ => ?_
      rw [← mul_one (z s), ← smul_eq_mul, ← Finsupp.smul_single]
      refine Submodule.smul_mem_smul (Ideal.Quotient.eq_zero_iff_mem.mp ?_) trivial
      simpa using DFunLike.congr_fun h2 s

theorem flat_of_isWeaklyRegular_of_le_jacobson [IsNoetherianRing A] [IsLocalRing A] (B : Type*)
    [CommRing B] [IsNoetherianRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (hB : (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    {xs : List A} (hxs : Ideal.ofList xs = maximalIdeal A) (h : IsWeaklyRegular M xs) :
    Module.Flat A M := by
  have he : Ideal.span (Set.range xs.get) = maximalIdeal A := by
    rw [← ofList_ofFn_eq_span_range, List.ofFn_get, hxs]
  refine (isQuasiRegularSeq_get_of_isWeaklyRegular h).flat_of_isMaximal B ?_ ?_ <;> rw [he]
  exacts [inferInstance, hB]

theorem flat_of_isWeaklyRegular_of_isLocalHom [IsNoetherianRing A] [IsLocalRing A] (B : Type*)
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {xs : List A} (hxs : Ideal.ofList xs = maximalIdeal A) (h : IsWeaklyRegular M xs) :
    Module.Flat A M :=
  flat_of_isWeaklyRegular_of_le_jacobson B
    ((map_maximalIdeal_le _).trans (maximalIdeal_le_jacobson _)) hxs h

end Flat

section Domain

variable {R : Type*} [CommRing R]

theorem isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) :=
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr fun h =>
    hx (Ideal.span_singleton_eq_top.mp h)
  .of_surjective' _ Ideal.Quotient.mk_surjective

theorem ofList_map_mk_eq_maximalIdeal [IsLocalRing R] {x : R} {xs : List R}
    (h : Ideal.ofList (x :: xs) = maximalIdeal R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) = maximalIdeal _ := by
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← h, Ideal.ofList_cons,
    Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_ofList]

theorem exists_ofList_cons_eq_maximalIdeal [IsLocalRing R] {xs : List R}
    (h : Ideal.ofList xs = maximalIdeal R) {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ ys : List R, ys.length + 1 = xs.length ∧ Ideal.ofList (x :: ys) = maximalIdeal R := by
  classical
  have he : Ideal.span (Set.range xs.get) = maximalIdeal R := by
    rw [← ofList_ofFn_eq_span_range, List.ofFn_get, h]
  have hmem : ∀ i, xs.get i ∈ maximalIdeal R := fun i => he ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (he.symm ▸ hx)
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (a i) := by
    by_contra! hne
    refine hx2 (ha ▸ Ideal.sum_mem _ fun i _ => ?_)
    rw [pow_two]
    exact Ideal.mul_mem_mul (hne i) (hmem i)
  refine ⟨xs.eraseIdx i, List.length_eraseIdx_add_one i.2, le_antisymm ?_ ?_⟩
  · rw [Ideal.ofList_cons, sup_le_iff, Ideal.span_singleton_le_iff_mem, ← h]
    exact ⟨h.symm ▸ hx, Ideal.span_mono fun y hy => List.mem_of_mem_eraseIdx hy⟩
  · have hj : ∀ j, j ≠ i → xs.get j ∈ Ideal.ofList (x :: xs.eraseIdx i) := fun j hj =>
      Ideal.subset_span (List.mem_cons_of_mem _
        (List.mem_eraseIdx_iff_getElem.mpr ⟨j, j.2, fun e => hj (Fin.ext e), rfl⟩))
    rw [← he, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    swap
    · exact hj j hji
    subst hji
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hi]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at ha
    rw [eq_sub_of_add_eq ha]
    exact sub_mem (Ideal.subset_span List.mem_cons_self)
      (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ (hj k (Finset.ne_of_mem_erase hk)))

universe u in
private theorem is_domain_of_regular_local (n : ℕ) : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (xs : List R), xs.length = n → Ideal.ofList xs = maximalIdeal R →
    (n : WithBot ℕ∞) ≤ ringKrullDim R → IsDomain R := by
  induction n with
  | zero =>
    intro R _ _ _ xs hn h _
    rw [List.length_eq_zero_iff.mp hn, Ideal.ofList_nil] at h
    exact (isField_iff_maximalIdeal_eq.mpr h.symm).isDomain
  | succ n ih =>
    intro R _ _ _ xs hn h hd
    have hmin : maximalIdeal R ∉ minimalPrimes R := by
      intro hm
      have h0 : ringKrullDim R = 0 := by
        rw [← maximalIdeal_height_eq_ringKrullDim, Ideal.height_eq_zero_iff.mpr hm]
        rfl
      rw [h0] at hd
      norm_cast at hd
    obtain ⟨x, hx, hx'⟩ : ∃ x ∈ maximalIdeal R,
        ∀ p ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R), x ∉ p := by
      by_contra! hne
      obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite
        ((minimalPrimes.finite_of_isNoetherianRing R).insert (maximalIdeal R ^ 2))
        (f := id) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) (I := maximalIdeal R)
        (fun p hp h1 _ => (hp.resolve_left h1).1.1)).mp fun x hx => by simpa using hne x hx
      rcases hp with rfl | hp
      · have hb : maximalIdeal R = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (maximalIdeal R) _ (IsNoetherian.noetherian _) (by simpa [pow_two] using hle)
          (maximalIdeal_le_jacobson _)
        exact hmin ⟨⟨inferInstance, bot_le⟩, fun q _ _ => hb ▸ bot_le⟩
      · exact hmin (((maximalIdeal.isMaximal R).eq_of_le hp.1.1.ne_top hle).symm ▸ hp)
    obtain ⟨ys, hys, hgen⟩ := exists_ofList_cons_eq_maximalIdeal h hx (hx' _ (.inl rfl))
    have := isLocalRing_quotient_span_singleton hx
    have hdom : IsDomain (R ⧸ Ideal.span {x}) := by
      refine ih _ _ (by simp; omega) (ofList_map_mk_eq_maximalIdeal hgen) ?_
      have := hd.trans (ringKrullDim_le_ringKrullDim_quotient_add_card {x}
        (by simpa [ringJacobson_eq_maximalIdeal] using hx))
      rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_add] at this
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp this
    have hp : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hpm, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Ideal.span {x}) bot_le
    have hb : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
        (IsNoetherian.noetherian _) (fun y hy => ?_) (maximalIdeal_le_jacobson _)
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp (hle hy)
      exact Ideal.mul_mem_mul hx ((hpm.1.1.mem_or_mem hy).resolve_left (hx' p (.inr hpm)))
    have : (⊥ : Ideal R).IsPrime := hb ▸ hpm.1.1
    exact IsDomain.of_bot_isPrime R

theorem exists_ofList_eq_maximalIdeal_length_eq (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    ∃ xs : List R, Ideal.ofList xs = maximalIdeal R ∧ (xs.length : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  refine ⟨s.toList, ?_, ?_⟩
  · rw [← hspan, Ideal.ofList]
    congr 1
    ext
    simp
  · rw [Finset.length_toList, hs, IsRegularLocalRing.spanFinrank_maximalIdeal]

theorem isDomain_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  exact is_domain_of_regular_local _ R xs rfl h hd.le

universe u in
private theorem is_weakly_regular_of_system_parameters (n : ℕ) : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (xs : List R), xs.length = n → Ideal.ofList xs = maximalIdeal R →
    (n : WithBot ℕ∞) ≤ ringKrullDim R → IsWeaklyRegular R xs := by
  induction n with
  | zero =>
    intro R _ _ _ xs hn h _
    rw [List.length_eq_zero_iff.mp hn]
    exact .nil R R
  | succ n ih =>
    intro R _ _ _ xs hn h hd
    have := is_domain_of_regular_local _ R xs hn h hd
    obtain _ | ⟨x, ys⟩ := xs
    · simp at hn
    have hx : x ∈ maximalIdeal R := h ▸ Ideal.subset_span List.mem_cons_self
    have := isLocalRing_quotient_span_singleton hx
    have hn' : (ys.map (Ideal.Quotient.mk (Ideal.span {x}))).length = n := by simpa using hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h1 : Ideal.ofList ys = maximalIdeal R := by simpa using h
      have h2 := hd.trans (ringKrullDim_le_spanFinrank_maximalIdeal R)
      have h3 : (maximalIdeal R).spanFinrank ≤ ys.length := by
        classical
        rw [← h1]
        refine (Submodule.spanFinrank_span_le_ncard_of_finite (List.finite_toSet ys)).trans ?_
        rw [← List.coe_toFinset, Set.ncard_coe_finset]
        exact List.toFinset_card_le ys
      norm_cast at h2
      simp at hn
      omega
    have hq : IsWeaklyRegular (R ⧸ Ideal.span {x}) (ys.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
      refine ih _ _ hn' (ofList_map_mk_eq_maximalIdeal h) ?_
      have := hd.trans (ringKrullDim_le_ringKrullDim_quotient_add_card {x}
        (by simpa [ringJacobson_eq_maximalIdeal] using hx))
      rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_add] at this
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp this
    rw [isWeaklyRegular_cons_iff]
    refine ⟨IsSMulRegular.of_ne_zero hx0, ?_⟩
    have e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [e.isWeaklyRegular_congr, ← isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x})]
    exact hq

theorem isRegular_of_ofList_eq_maximalIdeal [IsNoetherianRing R] [IsLocalRing R] {xs : List R}
    (h : Ideal.ofList xs = maximalIdeal R) (hd : (xs.length : WithBot ℕ∞) ≤ ringKrullDim R) :
    RingTheory.Sequence.IsRegular R xs :=
  (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    fun _ hx => h ▸ Ideal.subset_span hx).mpr (is_weakly_regular_of_system_parameters _ R xs rfl h hd)

theorem isRegular_of_length_eq_spanFinrank [IsRegularLocalRing R] {xs : List R}
    (h : Ideal.ofList xs = maximalIdeal R) (hd : xs.length = (maximalIdeal R).spanFinrank) :
    RingTheory.Sequence.IsRegular R xs :=
  isRegular_of_ofList_eq_maximalIdeal h (by rw [hd, IsRegularLocalRing.spanFinrank_maximalIdeal])

end Domain

section Depth

universe u v

open CategoryTheory Abelian

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem length_le_ringKrullDim_quotient_of_isAssociatedPrime {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] {xs : List R} (hm : ∀ x ∈ xs, x ∈ maximalIdeal R)
    (h : IsWeaklyRegular M xs) {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (xs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have hco : ∀ (q : Ideal R) (hq : q.IsPrime),
      ringKrullDim (R ⧸ q) = Order.coheight (⟨q, hq⟩ : PrimeSpectrum R) := fun q hq => by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  induction xs generalizing M p with
  | nil =>
    rw [hco p hp.isPrime]
    exact WithBot.coe_le_coe.mpr zero_le
  | cons x xs ih =>
    rw [isWeaklyRegular_cons_iff] at h
    have hx : x ∈ maximalIdeal R := hm x List.mem_cons_self
    obtain ⟨hpp, y, hy⟩ := isAssociatedPrime_iff.mp hp
    have hy' : ∀ r, r ∈ p ↔ r • y = 0 := fun r => by simp [hy]
    have hy0 : y ≠ 0 := fun h0 => hpp.ne_top (by ext r; simp [hy', h0])
    obtain ⟨z, hz, hzx⟩ : ∃ z : M, (∀ r ∈ p, r • z = 0) ∧
        (Submodule.Quotient.mk z : QuotSMulTop x M) ≠ 0 := by
      by_contra! hne
      let N : Submodule R M := Submodule.torsionBySet R M p
      have hN : N = ⊥ := by
        refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
          (IsNoetherian.noetherian _) (fun z hz => ?_) (maximalIdeal_le_jacobson _)
        have hz' : ∀ r ∈ p, r • z = 0 := fun r hr =>
          (Submodule.mem_torsionBySet_iff _ _).mp hz ⟨r, hr⟩
        obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
          ((Submodule.Quotient.mk_eq_zero _).mp (hne z hz'))
        refine Submodule.smul_mem_smul hx ((Submodule.mem_torsionBySet_iff _ _).mpr fun r => ?_)
        exact h.1.right_eq_zero_of_smul (by rw [smul_comm]; exact hz' r r.2)
      exact hy0 ((Submodule.mem_bot R).mp (hN ▸ (Submodule.mem_torsionBySet_iff _ _).mpr
        fun r => (hy' r).mp r.2))
    obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hzx
    have hpq : p ≤ q := fun r hr => hle (by
      simp [← Submodule.Quotient.mk_smul, hz r hr])
    have hxq : x ∈ q := hle (by
      simp [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.smul_mem_pointwise_smul])
    have hxp : x ∉ p := fun hxp => hy0 (h.1.right_eq_zero_of_smul ((hy' x).mp hxp))
    have h1 := ih (fun r hr => hm r (List.mem_cons_of_mem _ hr)) h.2 hq
    have h2 := Order.coheight_add_one_le
      (show (⟨p, hpp⟩ : PrimeSpectrum R) < ⟨q, hq.isPrime⟩ from
        lt_of_le_of_ne hpq fun e => hxp ((show p = q from congrArg PrimeSpectrum.asIdeal e) ▸ hxq))
    rw [hco q hq.isPrime] at h1
    rw [hco p hpp, List.length_cons, Nat.cast_add_one]
    refine (add_le_add_left h1 1).trans ?_
    exact_mod_cast h2

theorem exists_isRegular_quotSMulTop [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (h : RingTheory.Sequence.IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ maximalIdeal R) (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ RingTheory.Sequence.IsRegular (QuotSMulTop y M) zs := by
  first
  | exact @_root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop
  | exact _root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop
  | (apply _root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop <;> assumption)
  | (intros; apply _root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop ..)

theorem supportDim_le_supportDim_quotient_add_length {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {ys : List R} (hm : ∀ y ∈ ys, y ∈ maximalIdeal R) :
    Module.supportDim R M ≤
      Module.supportDim R (M ⧸ Ideal.ofList ys • (⊤ : Submodule R M)) + ys.length := by
  induction ys generalizing M with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    simpa using (Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)).ge
  | cons y ys ih =>
    rw [Module.supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y _),
      List.length_cons, Nat.cast_add_one, ← add_assoc]
    exact (Module.supportDim_le_supportDim_quotSMulTop_succ (hm y List.mem_cons_self)).trans
      (add_le_add_left (ih fun r hr => hm r (List.mem_cons_of_mem _ hr)) 1)

theorem isRegular_of_supportDim_quotient_add_length_le [Small.{v} R] {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Finite R M] {xs : List R} (h : RingTheory.Sequence.IsRegular M xs)
    {ys : List R} (hm : ∀ y ∈ ys, y ∈ maximalIdeal R)
    (hd : Module.supportDim R (M ⧸ Ideal.ofList ys • (⊤ : Submodule R M)) + ys.length ≤
      xs.length) : RingTheory.Sequence.IsRegular M ys := by
  induction ys generalizing M xs with
  | nil =>
    have := h.nontrivial
    exact .nil R M
  | cons y ys ih =>
    have := h.nontrivial
    have hy : y ∈ maximalIdeal R := hm y List.mem_cons_self
    have hm' : ∀ r ∈ ys, r ∈ maximalIdeal R := fun r hr => hm r (List.mem_cons_of_mem _ hr)
    have hxs : ∀ x ∈ xs, x ∈ maximalIdeal R := fun x hx =>
      le_maximalIdeal (J := Ideal.ofList xs) (fun e => h.2 (by simp [e])) (Ideal.subset_span hx)
    rw [Module.supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y _),
      List.length_cons, Nat.cast_add_one, ← add_assoc] at hd
    have hq : Module.supportDim R (QuotSMulTop y M) + 1 ≤ xs.length :=
      (add_le_add_left (supportDim_le_supportDim_quotient_add_length hm') 1).trans hd
    have hreg : IsSMulRegular M y := by
      by_contra hne
      have : y ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_regular R M]
        exact hne
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp this
      have h1 := length_le_ringKrullDim_quotient_of_isAssociatedPrime hxs h.1 hp
      have h2 : ringKrullDim (R ⧸ p) ≤ Module.supportDim R (QuotSMulTop y M) := by
        rw [ringKrullDim_quotient, Module.supportDim]
        refine Order.krullDim_le_of_strictMono (Set.inclusion fun q hq => ?_) fun _ _ h => h
        rw [Module.support_quotSMulTop]
        refine ⟨Module.mem_support_iff_of_finite.mpr (le_trans ?_ hq), ?_⟩
        · simpa [Submodule.annihilator_top] using IsAssociatedPrime.annihilator_le hp
        · simpa using hq hyp
      have h3 := (add_le_add_left (h1.trans h2) 1).trans hq
      norm_cast at h3
      omega
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hy
    obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
      refine Nat.exists_eq_add_one_of_ne_zero fun h0 => ?_
      rw [h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff] at hq
      exact Module.supportDim_ne_bot_of_nontrivial R _ hq
    obtain ⟨zs, hzs, hz⟩ := exists_isRegular_quotSMulTop h hn.ge hy hreg
    rw [isRegular_cons_iff]
    refine ⟨hreg, ih hz hm' ?_⟩
    rw [hn, ← hzs, ← Nat.cast_one, Nat.cast_add] at hd
    exact ENat.WithBot.add_le_add_natCast_right_iff.mp hd

end Depth

section Miracle

open ReciprocityTheory.CA

variable {R : Type*} [CommRing R]

theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  exact ⟨inferInstance, xs.length, hd.symm, xs, rfl, fun _ hx => h ▸ Ideal.subset_span hx,
    isRegular_of_ofList_eq_maximalIdeal h hd.le⟩

theorem isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le [IsLocalRing R] (hR : IsCM R)
    {ys : List R} (hm : ∀ y ∈ ys, y ∈ maximalIdeal R)
    (hd : ringKrullDim (R ⧸ Ideal.ofList ys) + ys.length ≤ ringKrullDim R) :
    RingTheory.Sequence.IsRegular R ys := by
  obtain ⟨_, n, hn, xs, rfl, -, hxs⟩ := hR
  refine isRegular_of_supportDim_quotient_add_length_le hxs hm ?_
  rwa [← hn, smul_eq_mul, Ideal.mul_top, Module.supportDim_quotient_eq_ringKrullDim]

theorem ringKrullDim_quotient_le_zero_of_forall_eq [IsLocalRing R] {I : Ideal R}
    (h : ∀ p : Ideal R, p.IsPrime → I ≤ p → p = maximalIdeal R) : ringKrullDim (R ⧸ I) ≤ 0 := by
  rw [ringKrullDim_quotient]
  have : Subsingleton (PrimeSpectrum.zeroLocus (R := R) I) :=
    ⟨fun p q => Subtype.ext (PrimeSpectrum.ext ((h _ p.1.2 p.2).trans (h _ q.1.2 q.2).symm))⟩
  exact Order.krullDim_nonpos_of_subsingleton

theorem isRegular_of_isCM_of_radical_eq [IsLocalRing R] (hR : IsCM R) {ys : List R}
    (hr : (Ideal.ofList ys).radical = maximalIdeal R)
    (hd : (ys.length : WithBot ℕ∞) ≤ ringKrullDim R) : RingTheory.Sequence.IsRegular R ys := by
  refine isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le hR
    (fun y hy => hr ▸ Ideal.le_radical (Ideal.subset_span hy)) ?_
  have := ringKrullDim_quotient_le_zero_of_forall_eq (I := Ideal.ofList ys) fun p hp hle =>
    ((maximalIdeal.isMaximal R).eq_of_le hp.ne_top (hr ▸ hp.radical_le_iff.mpr hle)).symm
  exact (add_le_add_left this _).trans (by rwa [zero_add])

theorem isRegular_of_radical_eq_maximalIdeal [IsRegularLocalRing R] {ys : List R}
    (hr : (Ideal.ofList ys).radical = maximalIdeal R)
    (hd : (ys.length : WithBot ℕ∞) ≤ ringKrullDim R) : RingTheory.Sequence.IsRegular R ys :=
  isRegular_of_isCM_of_radical_eq (isCM_of_isRegularLocalRing R) hr hd

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem flat_of_isCM_of_ringKrullDim_add_le [IsRegularLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] (hB : IsCM B)
    (hd : ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤
      ringKrullDim B) : Module.Flat A B := by
  have := hB.1
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq A
  refine flat_of_isWeaklyRegular_of_isLocalHom B h ?_
  rw [← isWeaklyRegular_map_algebraMap_iff B]
  refine (isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le hB (fun y hy => ?_) ?_).1
  · refine map_maximalIdeal_le (algebraMap A B) ?_
    rw [← h, Ideal.map_ofList]
    exact Ideal.subset_span hy
  · rwa [← Ideal.map_ofList, h, List.length_map, hl, add_comm]

theorem ringKrullDim_quotient_map_maximalIdeal_le_zero [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] :
    ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤ 0 := by
  refine ringKrullDim_quotient_le_zero_of_forall_eq fun p hp hle => ?_
  refine Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) _ _ (le_maximalIdeal hp.ne_top) ?_
  exact ((maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hp.ne_top)
    (Ideal.map_le_iff_le_comap.mp hle)).symm.trans (maximalIdeal_comap _).symm

theorem flat_of_isCM_of_quasiFinite [IsRegularLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] (hB : IsCM B)
    (hd : ringKrullDim A ≤ ringKrullDim B) : Module.Flat A B :=
  flat_of_isCM_of_ringKrullDim_add_le hB
    ((add_le_add_right ringKrullDim_quotient_map_maximalIdeal_le_zero _).trans (by rwa [add_zero]))

theorem flat_of_isRegularLocalRing_of_quasiFinite [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Flat A B :=
  flat_of_isCM_of_quasiFinite (isCM_of_isRegularLocalRing B) hd.le

theorem free_of_isRegularLocalRing_of_finite [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Free A B :=
  have := flat_of_isRegularLocalRing_of_quasiFinite hd
  Module.free_of_flat_of_isLocalRing

theorem flat_localization_atPrime_of_isCM (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    [q.LiesOver p] [IsRegularLocalRing (Localization.AtPrime p)] [Algebra.QuasiFiniteAt A q]
    (hB : IsCM (Localization.AtPrime q)) (hd : p.height ≤ q.height) :
    Module.Flat A (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.QuasiFinite (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars A _ _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    refine flat_of_isCM_of_quasiFinite hB ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
      IsLocalization.AtPrime.ringKrullDim_eq_height q]
    exact WithBot.coe_le_coe.mpr hd
  exact .trans A (Localization.AtPrime p) _

theorem flat_of_isRegularRing_of_isCM [IsRegularRing A] [Algebra.QuasiFinite A B]
    (hB : ∀ (q : Ideal B) [q.IsMaximal], IsCM (Localization.AtPrime q))
    (hd : ∀ q : Ideal B, q.IsMaximal → (q.under A).height ≤ q.height) : Module.Flat A B :=
  Module.flat_of_isLocalized_maximal B B (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap B (Localization.AtPrime q))
    fun q hq => flat_localization_atPrime_of_isCM (q.under A) q (hB q) (hd q hq)

theorem flat_of_isRegularRing_of_isRegularRing [IsRegularRing A] [IsRegularRing B]
    [Algebra.QuasiFinite A B]
    (hd : ∀ q : Ideal B, q.IsMaximal → (q.under A).height ≤ q.height) : Module.Flat A B :=
  flat_of_isRegularRing_of_isCM (fun _ _ => isCM_of_isRegularLocalRing _) hd

example (p : ℕ) [Fact p.Prime] : RingTheory.Sequence.IsRegular ℤ_[p] [(p : ℤ_[p]) ^ 2] := by
  refine isRegular_of_radical_eq_maximalIdeal ?_ ?_
  · rw [Ideal.ofList_singleton, ← Ideal.span_singleton_pow, Ideal.radical_pow _ two_ne_zero,
      ← PadicInt.maximalIdeal_eq_span_p, (maximalIdeal.isMaximal _).isPrime.radical]
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

end Miracle

end GlobalTheory
