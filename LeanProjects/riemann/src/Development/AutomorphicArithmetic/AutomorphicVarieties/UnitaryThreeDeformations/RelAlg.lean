import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

namespace UpperTheory.V.UnitaryThreeInertia.Rel

theorem exists_eq_sum_X {O σ : Type} [CommRing O] [Fintype σ] (p : MvPowerSeries σ O) :
    ∃ g : σ → MvPowerSeries σ O, p = C (coeff 0 p) + ∑ i, X i * g i ∧
      ∀ i m, coeff m (g i) = 0 ∨ coeff m (g i) = coeff (Finsupp.single i 1 + m) p := by
  classical
  have hc : ∀ n : σ →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0 := fun n hn => by
    by_contra h
    push Not at h
    exact hn (Finsupp.ext h)
  choose c hc using hc
  let q : σ → MvPowerSeries σ O := fun i n =>
    if h : n ≠ 0 then (if c n h = i then coeff n p else 0) else 0
  have hq : ∀ i n, coeff n (q i) =
      if h : n ≠ 0 then (if c n h = i then coeff n p else 0) else 0 := fun _ _ => rfl
  have hd : ∀ i, X i ∣ q i := fun i => by
    rw [X_dvd_iff]
    intro m hm
    rw [hq]
    split_ifs with h1 h2
    · exact absurd (h2 ▸ hm) (hc m h1)
    · rfl
    · rfl
  choose g hg using hd
  refine ⟨g, ?_, fun i m => ?_⟩
  · ext n
    simp only [← hg]
    rw [map_add, map_sum, coeff_C]
    simp only [hq]
    by_cases h : n ≠ 0
    · simp [dif_pos h, if_neg h]
    · simp only [dif_neg h, Finset.sum_const_zero]
      push Not at h
      subst h
      simp
  · have h1 : coeff (Finsupp.single i 1 + m) (q i) = coeff m (g i) := by
      rw [hg, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h1, hq]
    split_ifs <;> simp

theorem mem_pow_of_coeff {O σ : Type} [CommRing O] [Fintype σ] (a : Ideal O) (M : Ideal (MvPowerSeries σ O))
    (hC : ∀ c ∈ a, C c ∈ M) (hX : ∀ i, X i ∈ M) :
    ∀ (N : ℕ) (f : MvPowerSeries σ O), (∀ n, coeff n f ∈ a ^ (N - Finsupp.degree n)) → f ∈ M ^ N := by
  intro N
  induction N with
  | zero => intro f _; simp
  | succ N ih =>
    intro f hf
    obtain ⟨g, h1, h2⟩ := exists_eq_sum_X f
    rw [h1]
    refine add_mem ?_ (Ideal.sum_mem _ fun i _ => ?_)
    · have h0 := hf 0
      simp only [map_zero, Nat.sub_zero] at h0
      have hle : a ≤ M.comap (C : O →+* MvPowerSeries σ O) := hC
      exact (Ideal.pow_right_mono hle _).trans (Ideal.le_comap_pow _ _) h0
    · rw [pow_succ']
      refine Ideal.mul_mem_mul (hX i) (ih _ fun n => ?_)
      rcases h2 i n with h | h
      · rw [h]; exact zero_mem _
      · have := hf (Finsupp.single i 1 + n)
        rw [map_add, Finsupp.degree_single, show N + 1 - (1 + Finsupp.degree n) = N - Finsupp.degree n by omega] at this
        rwa [h]

def Tr {O : Type} (σ : Type) [CommRing O] (a : Ideal O) (N : ℕ) : Ideal (MvPowerSeries σ O) where
  carrier := {f | ∀ n, coeff n f ∈ a ^ (N - Finsupp.degree n)}
  add_mem' ha hb n := by rw [map_add]; exact add_mem (ha n) (hb n)
  zero_mem' n := by simp
  smul_mem' g f hf n := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ (hf p.2))
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add]
    omega

theorem isHomog_Tr {O σ : Type} [CommRing O] (a : Ideal O) (N : ℕ) (wt : σ → ℤ) : IsHomog O wt (Tr σ a N) := by
  intro f hf j n
  rw [coeff_wcomp]
  split_ifs
  · exact hf n
  · exact zero_mem _

theorem finite_quot_Tr {O σ : Type} [CommRing O] [Finite σ] (a : Ideal O) (N : ℕ) [Finite (O ⧸ a ^ N)] :
    Finite (MvPowerSeries σ O ⧸ Tr σ a N) := by
  haveI : Finite {n : σ →₀ ℕ | Finsupp.degree n < N} := (Finsupp.finite_of_degree_lt N).to_subtype
  choose s hs using Ideal.Quotient.mk_surjective (I := Tr σ a N)
  refine Finite.of_injective (fun x (n : {n : σ →₀ ℕ | Finsupp.degree n < N}) =>
    Ideal.Quotient.mk (a ^ N) (coeff n.1 (s x))) fun x y h => ?_
  rw [← hs x, ← hs y, Ideal.Quotient.eq]
  intro n
  by_cases hn : Finsupp.degree n < N
  · have := Ideal.Quotient.eq.1 (congrFun h ⟨n, hn⟩)
    rw [map_sub]
    exact Ideal.pow_le_pow_right (Nat.sub_le _ _) this
  · rw [show N - Finsupp.degree n = 0 by omega]
    simp

theorem wcomp_of_mem {O σ : Type} [CommRing O] (wt : σ → ℤ) {j : ℤ} {f : MvPowerSeries σ O}
    (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  ext n
  rw [coeff_wcomp]
  split_ifs with h
  · rfl
  · exact (hf n h).symm

theorem wcomp_of_ne {O σ : Type} [CommRing O] (wt : σ → ℤ) {i j : ℤ} (h : i ≠ j) {f : MvPowerSeries σ O}
    (hf : f ∈ wtPart O wt i) : wcomp O wt j f = 0 := by
  ext n
  rw [coeff_wcomp]
  split_ifs with h'
  · exact hf n (h' ▸ h.symm)
  · rfl

theorem exists_sub_sum_mem_Tr {O σ : Type} [CommRing O] [Finite σ] (a : Ideal O) (N : ℕ) (wt : σ → ℤ)
    (f : MvPowerSeries σ O) : ∃ S : Finset ℤ, f - ∑ j ∈ S, wcomp O wt j f ∈ Tr σ a N := by
  classical
  refine ⟨(Finsupp.finite_of_degree_lt (σ := σ) N).toFinset.image (Finsupp.weight wt), fun n => ?_⟩
  by_cases hn : Finsupp.degree n < N
  · rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_eq_single (Finsupp.weight wt n), if_pos rfl, sub_self]
    · exact zero_mem _
    · exact fun j _ hj => if_neg hj.symm
    · exact fun h => absurd (Finset.mem_image_of_mem _ (by simpa using hn)) h
  · rw [show N - Finsupp.degree n = 0 by omega]
    simp

theorem nonempty_gradedAlgebra_map {O A B : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    (𝒜 : ℤ → Submodule O A) [SetLike.GradedMonoid 𝒜] (e : ℤ → A →ₗ[O] A)
    (h1 : ∀ j, ∀ x ∈ 𝒜 j, e j x = x) (h2 : ∀ i j, i ≠ j → ∀ x ∈ 𝒜 i, e j x = 0) (φ : A →ₐ[O] B)
    (hk : ∀ j x, φ x = 0 → φ (e j x) = 0) (ht : ⨆ j, (𝒜 j).map φ.toLinearMap = ⊤) :
    Nonempty (GradedAlgebra fun j => (𝒜 j).map φ.toLinearMap) := by
  have hi : DirectSum.IsInternal fun j => (𝒜 j).map φ.toLinearMap := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨fun j => ?_, ht⟩
    rw [Submodule.disjoint_def]
    rintro _ ⟨f, hf, rfl⟩ hx
    have hle : (⨆ i, ⨆ (_ : i ≠ j), (𝒜 i).map φ.toLinearMap) ≤ (LinearMap.ker (e j)).map φ.toLinearMap :=
      iSup₂_le fun i hi => Submodule.map_mono fun x hx => h2 i j hi x hx
    obtain ⟨g, hg, hfg⟩ := hle hx
    have h3 := hk j (f - g) (by rw [map_sub]; exact sub_eq_zero.2 hfg.symm)
    rw [map_sub, h1 j f hf, LinearMap.mem_ker.1 hg, sub_zero] at h3
    exact h3
  haveI : SetLike.GradedMonoid fun j => (𝒜 j).map φ.toLinearMap :=
    { one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one φ⟩
      mul_mem := by
        rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, SetLike.GradedMul.mul_mem hf hg, map_mul φ f g⟩ }
  exact ⟨{ hi.chooseDecomposition with }⟩

theorem isCO_of_surj {O A B : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsLocalRing A]
    [IsLocalHom (algebraMap O A)] (hr : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ maximalIdeal A)
    [CommRing B] [Algebra O B] [Finite B] [Nontrivial B] (φ : A →ₐ[O] B) (hφ : Function.Surjective φ) :
    IsCO O B := by
  haveI : IsLocalRing B := IsLocalRing.of_surjective' (φ : A →+* B) hφ
  haveI : IsLocalHom (φ : A →+* B) := IsLocalHom.of_surjective _ hφ
  have hl : IsLocalHom (algebraMap O B) := by
    rw [← φ.comp_algebraMap]
    infer_instance
  refine { complete := inferInstance, isLocalHom := hl, res_surj := fun x => ?_ }
  obtain ⟨y, rfl⟩ := hφ x
  obtain ⟨a, ha⟩ := hr y
  refine ⟨a, ?_⟩
  have := map_nonunit (φ : A →+* B) _ ha
  simpa using this

theorem exists_span_of_card_le {O M : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [AddCommGroup M]
    [Module O M] [Finite M] (hk : ∀ c ∈ maximalIdeal O, ∀ x : M, c • x = 0) (n : ℕ)
    (hc : Nat.card M ≤ Nat.card (ResidueField O) ^ n) :
    ∃ f : Fin n → M, Submodule.span O (Set.range f) = ⊤ := by
  have ht : Module.IsTorsionBySet O M (maximalIdeal O) := fun x a => hk a.1 a.2 x
  letI : Module (ResidueField O) M := ht.module
  haveI : IsScalarTower O (ResidueField O) M := ht.isScalarTower
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O)] at hc
  have hd := (Nat.pow_le_pow_iff_right Finite.one_lt_card).1 hc
  let b := Module.finBasis (ResidueField O) M
  refine ⟨fun i => if h : i.1 < Module.finrank (ResidueField O) M then b ⟨i, h⟩ else 0, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := residue_surjective (b.repr x i)
  rw [← hc, show residue O c = algebraMap O (ResidueField O) c from rfl, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.1, lt_of_lt_of_le i.2 hd⟩, by simp⟩)

section Fin

variable {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A]
  (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

theorem mem_max_of_ne [Finite A] {j : ℤ} (hj : j ≠ 0) {x : A} (hx : x ∈ 𝒜 j) : x ∈ maximalIdeal A := by
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => x ^ n
  have ha : x ^ a ∈ 𝒜 (a • j) := SetLike.pow_mem_graded a hx
  have hb : x ^ a ∈ 𝒜 (b • j) := by rw [h]; exact SetLike.pow_mem_graded b hx
  have hne : a • j ≠ b • j := fun e => hab (by
    simp only [nsmul_eq_mul] at e
    exact_mod_cast mul_right_cancel₀ hj e)
  have h0 : x ^ a = 0 := by
    rw [← DirectSum.decompose_of_mem_same 𝒜 hb, DirectSum.decompose_of_mem_ne 𝒜 ha hne]
  intro hu
  exact (hu.pow a).ne_zero h0

theorem max_isHomogeneous [Finite A] : (maximalIdeal A).IsHomogeneous 𝒜 := by
  classical
  intro j x hx
  by_cases hj : j = 0
  · subst hj
    by_cases h0 : (0 : ℤ) ∈ (DirectSum.decompose 𝒜 x).support
    · have h := DirectSum.sum_support_decompose 𝒜 x
      rw [← Finset.add_sum_erase _ _ h0] at h
      rw [eq_sub_of_add_eq h]
      exact sub_mem hx (Ideal.sum_mem _ fun i hi => mem_max_of_ne 𝒜 (Finset.ne_of_mem_erase hi) (SetLike.coe_mem _))
    · rw [DFinsupp.notMem_support_iff.1 h0]
      exact zero_mem _
  · exact mem_max_of_ne 𝒜 hj (SetLike.coe_mem _)

def Kj (J : Ideal A) (j : ℤ) : Ideal A := maximalIdeal A * J ⊔ Ideal.span {x | x ∈ J ∧ ∃ i, i ≠ j ∧ x ∈ 𝒜 i}

omit [GradedAlgebra 𝒜] in
theorem Kj_le (J : Ideal A) (j : ℤ) : Kj 𝒜 J j ≤ J :=
  sup_le Ideal.mul_le_right (Ideal.span_le.2 fun _ hx => hx.1)

theorem Kj_isHomogeneous [Finite A] {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (j : ℤ) : (Kj 𝒜 J j).IsHomogeneous 𝒜 :=
  ((max_isHomogeneous 𝒜).mul hJ).sup (Ideal.homogeneous_span 𝒜 _ fun _ hx => ⟨hx.2.choose, hx.2.choose_spec.2⟩)

theorem decompose_mem_of_mem_Kj [Finite A] {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (j : ℤ) {y : A}
    (hy : y ∈ Kj 𝒜 J j) : (DirectSum.decompose 𝒜 y j : A) ∈ maximalIdeal A * J := by
  have hm := (max_isHomogeneous 𝒜).mul hJ
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  refine add_mem (hm j ha) ?_
  clear hy
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨-, i, hi, hx⟩ := hx
    rw [DirectSum.decompose_of_mem_ne 𝒜 hx hi]
    exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem hx hy
  | smul c x hx h =>
    obtain ⟨d, hd⟩ := IsCO.res_surj (O := O) c
    have hxJ : x ∈ J := (Ideal.span_le.2 fun _ hx => hx.1) hx
    have e : c • x = d • x + (c - algebraMap O A d) * x := by rw [smul_eq_mul, Algebra.smul_def]; ring
    rw [e, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, DirectSum.decompose_smul,
      DirectSum.smul_apply, Submodule.coe_smul]
    exact add_mem (Submodule.smul_of_tower_mem _ d h) (hm j (Ideal.mul_mem_mul hd hxJ))

theorem sub_decompose_mem_Kj {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (j : ℤ) {x : A} (hx : x ∈ J) :
    x - (DirectSum.decompose 𝒜 x j : A) ∈ Kj 𝒜 J j := by
  classical
  have hs : ∀ i, i ≠ j → (DirectSum.decompose 𝒜 x i : A) ∈ Kj 𝒜 J j := fun i hi =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨hJ i hx, i, hi, SetLike.coe_mem _⟩)
  have h := DirectSum.sum_support_decompose 𝒜 x
  by_cases h0 : j ∈ (DirectSum.decompose 𝒜 x).support
  · rw [← Finset.add_sum_erase _ _ h0] at h
    rw [← eq_sub_of_add_eq' h]
    exact Ideal.sum_mem _ fun i hi => hs i (Finset.ne_of_mem_erase hi)
  · rw [DFinsupp.notMem_support_iff.1 h0, Submodule.coe_zero, sub_zero, ← h]
    exact Ideal.sum_mem _ fun i hi => hs i fun e => h0 (e ▸ hi)

theorem exists_gens_wt [Finite A] [Finite (ResidueField O)] {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (j : ℤ) (n : ℕ)
    (hc : Nat.card (J.map (Ideal.Quotient.mk (Kj 𝒜 J j))) ≤ Nat.card (ResidueField O) ^ n) :
    ∃ f : Fin n → A, (∀ i, f i ∈ J ∧ f i ∈ 𝒜 j) ∧
      ∀ x ∈ J, (DirectSum.decompose 𝒜 x j : A) ∈ Ideal.span (Set.range f) ⊔ maximalIdeal A * J := by
  set I := J.map (Ideal.Quotient.mk (Kj 𝒜 J j)) with hI
  have hl : ∀ y : I, ∃ x, (x ∈ J ∧ x ∈ 𝒜 j) ∧ Ideal.Quotient.mk (Kj 𝒜 J j) x = y := fun y => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 y.2
    refine ⟨_, ⟨hJ j hx, SetLike.coe_mem _⟩, ?_⟩
    rw [← e]
    exact (Ideal.Quotient.eq.2 (sub_decompose_mem_Kj 𝒜 hJ j hx)).symm
  choose s hs hs' using hl
  haveI : Finite (A ⧸ Kj 𝒜 J j) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨g, hg⟩ := exists_span_of_card_le (O := O) (M := I) (fun c hc y => Subtype.ext (by
    rw [Submodule.coe_smul_of_tower, ← hs' y, Submodule.coe_zero, ← Ideal.Quotient.mkₐ_eq_mk O, ← map_smul,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (map_nonunit _ _ hc) (hs y).1))) n hc
  refine ⟨fun i => s (g i), fun i => hs _, fun x hx => ?_⟩
  have hx' := hJ j hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1
    (hg ▸ Submodule.mem_top : (⟨_, Ideal.mem_map_of_mem _ hx'⟩ : I) ∈ Submodule.span O (Set.range g))
  have h1 : (DirectSum.decompose 𝒜 x j : A) - ∑ i, c i • s (g i) ∈ Kj 𝒜 J j := by
    rw [← Ideal.Quotient.eq]
    have := congrArg Subtype.val hc
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul_of_tower] at this
    rw [← this, ← Ideal.Quotient.mkₐ_eq_mk O, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Ideal.Quotient.mkₐ_eq_mk, hs']
  have h2 := decompose_mem_of_mem_Kj 𝒜 hJ j h1
  rw [DirectSum.decompose_of_mem_same 𝒜 (sub_mem (SetLike.coe_mem _)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hs _).2))] at h2
  rw [← add_sub_cancel (∑ i, c i • s (g i)) (DirectSum.decompose 𝒜 x j : A)]
  exact Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨i, rfl⟩)) h2

theorem exists_gens [Finite A] [Finite (ResidueField O)] {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (n : ℤ → ℕ)
    (hc : ∀ j, Nat.card (J.map (Ideal.Quotient.mk (Kj 𝒜 J j))) ≤ Nat.card (ResidueField O) ^ n j) :
    ∃ f : (j : ℤ) → Fin (n j) → A, (∀ j i, f j i ∈ J ∧ f j i ∈ 𝒜 j) ∧
      J ≤ Ideal.span (⋃ j, Set.range (f j)) ⊔ maximalIdeal A * J := by
  classical
  choose f hf hf' using fun j => exists_gens_wt 𝒜 hJ j (n j) (hc j)
  refine ⟨f, hf, fun x hx => ?_⟩
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ =>
    sup_le_sup_right (Ideal.span_mono (Set.subset_iUnion (fun j => Set.range (f j)) j)) _ (hf' j x hx)

theorem nonempty_gradedAlgebra_quot {B : Type} [CommRing B] [Algebra O B] (φ : A →ₐ[O] B)
    (hφ : Function.Surjective φ) (hk : (RingHom.ker φ).IsHomogeneous 𝒜) :
    Nonempty (GradedAlgebra fun j => (𝒜 j).map φ.toLinearMap) := by
  classical
  refine nonempty_gradedAlgebra_map 𝒜 (GradedAlgebra.proj 𝒜) (fun j x hx => DirectSum.decompose_of_mem_same 𝒜 hx)
    (fun i j h x hx => DirectSum.decompose_of_mem_ne 𝒜 hx h) φ (fun j x hx => hk j hx) ?_
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hφ y
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum]
  exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨_, SetLike.coe_mem _, rfl⟩

end Fin

end UpperTheory.V.UnitaryThreeInertia.Rel
