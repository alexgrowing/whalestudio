import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.LinChange

theorem finsum_prod_fst {A B : Type} [Finite B] [Nonempty B] (g : A → ℂ) :
    ∑ᶠ p : A × B, g p.1 = (Nat.card B : ℂ) * ∑ᶠ a, g a := by
  classical
  by_cases h : (Function.support g).Finite
  · have h2 : (Function.support fun p : A × B => g p.1).Finite :=
      (h.prod (Set.finite_univ (α := B))).subset fun p hp => ⟨hp, trivial⟩
    rw [finsum_curry _ h2, mul_finsum]
    refine finsum_congr fun a => ?_
    have := Fintype.ofFinite B
    simp [finsum_eq_sum_of_fintype]
  · have h2 : ¬ (Function.support fun p : A × B => g p.1).Finite := fun h2 =>
      h ((h2.image Prod.fst).subset fun a ha => ⟨(a, Classical.arbitrary B), ha, rfl⟩)
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h2, mul_zero]

theorem finsum_quot_le {V : Type} [AddCommGroup V] (S P : AddSubgroup V) (hle : S ≤ P)
    (hi : S.relIndex P ≠ 0) (φ : V → ℂ) (hφ : ∀ x, ∀ y ∈ P, φ (x + y) = φ x) :
    ∑ᶠ q : V ⧸ S, φ q.out = (S.relIndex P : ℂ) * ∑ᶠ q : V ⧸ P, φ q.out := by
  have : Finite (P ⧸ S.addSubgroupOf P) := Nat.finite_of_card_ne_zero hi
  have h := finsum_prod_fst (B := P ⧸ S.addSubgroupOf P) (fun q : V ⧸ P => φ q.out)
  rw [← finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hle)] at h
  refine Eq.trans (finsum_congr fun q => ?_) h
  have h1 : (AddSubgroup.quotientEquivProdOfLE hle q).1 = (q.out : V ⧸ P) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul P q.out
  rw [h1, hy, hφ _ _ y.2]

theorem finsum_quot_map {V : Type} [AddCommGroup V] (S : AddSubgroup V) (T : V ≃+ V)
    (φ : V → ℂ) (hφ : ∀ x, ∀ y ∈ S.map T.toAddMonoidHom, φ (x + y) = φ x) :
    ∑ᶠ q : V ⧸ S, φ (T q.out) = ∑ᶠ q : V ⧸ S.map T.toAddMonoidHom, φ q.out := by
  rw [← finsum_comp_equiv (QuotientAddGroup.congr S (S.map T.toAddMonoidHom) T rfl).toEquiv]
  refine finsum_congr fun q => ?_
  have h1 : (QuotientAddGroup.congr S (S.map T.toAddMonoidHom) T rfl).toEquiv q
      = (T q.out : V ⧸ S.map T.toAddMonoidHom) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul (S.map T.toAddMonoidHom) (T q.out)
  rw [h1, hy, hφ _ _ y.2]

variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

theorem intM_nat_smul (M : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((M : K) • x) :=
  fun k i => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isIntegral_natCast M).mul (hx k i)

theorem mem_perSub_iff (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ x = (R : K) • y := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, fun _ _ => isIntegral_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, intM_add ha hb, by rw [smul_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, fun k i => (ha k i).neg, by rw [smul_neg]⟩

theorem exists_basis : ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (b : Module.Basis J ℚ (Matrix κ ι K)),
    ∀ x, x ∈ AddSubgroup.closure (Set.range b) ↔ IntM x := by
  classical
  refine ⟨_, inferInstance, inferInstance,
    (NumberField.integralBasis K).smulTower (Matrix.stdBasis K κ ι), fun x => ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Module.Basis.mem_span_iff_repr_mem]
  have key : ∀ a : K, IsIntegral ℤ a ↔
      ∀ j, (NumberField.integralBasis K).repr a j ∈ Set.range (algebraMap ℤ ℚ) := by
    intro a
    rw [← Module.Basis.mem_span_iff_repr_mem, NumberField.mem_span_integralBasis]
    exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ c.2⟩
  have hr : ∀ p : κ × ι, (Matrix.stdBasis K κ ι).repr x p = x p.1 p.2 := by
    intro p
    simp [Matrix.stdBasis]
  simp only [IntM, key, Module.Basis.smulTower_repr, hr]
  exact ⟨fun h k i j => h (j, (k, i)), fun h p => h p.2.1 p.2.2 p.1⟩

theorem exists_den (T : Matrix κ ι K →ₗ[ℚ] Matrix κ ι K) :
    ∃ M : ℕ, 0 < M ∧ ∀ y, IntM y → IntM ((M : K) • T y) := by
  classical
  obtain ⟨J, _, _, b, hb⟩ := exists_basis (K := K) (κ := κ) (ι := ι)
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K)
    (Finset.univ.image fun p : J × κ × ι => T (b p.1) p.2.1 p.2.2)
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun y hy => ?_⟩
  rw [← hb] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro k i
    have h := hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, k, i)))
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast] at h; exact h
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg
  | zero => rw [map_zero, smul_zero]; exact fun _ _ => isIntegral_zero
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact intM_add hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact fun k i => (hx k i).neg

theorem map_nat_smul (T : Matrix κ ι K →ₗ[ℚ] Matrix κ ι K) (M : ℕ) (y : Matrix κ ι K) :
    T ((M : K) • y) = (M : K) • T y := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem map_perSub_le (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) :
    (perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom ≤ perSub K κ ι R := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := (mem_perSub_iff _ _).1 hx
  refine (mem_perSub_iff _ _).2 ⟨_, hT y hy, ?_⟩
  rw [smul_smul, ← Nat.cast_mul]
  exact map_nat_smul T.toLinearMap _ _

theorem relIndex_map (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) :
    ((((perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom).relIndex (perSub K κ ι R) : ℕ) : ℚ)
      = (M : ℚ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
        |LinearMap.det T.toLinearMap| := by
  obtain ⟨J, _, _, b, hb⟩ := exists_basis (K := K) (κ := κ) (ι := ι)
  have hsc : ∀ N : ℕ, 0 < N → ∃ e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K,
      e.toLinearMap = (N : ℚ) • LinearMap.id := fun N hN =>
    ⟨LinearEquiv.smulOfNeZero ℚ _ (N : ℚ) (by exact_mod_cast hN.ne'), by ext; simp⟩
  have hcl : ∀ e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K, AddSubgroup.closure (Set.range (b.map e)) =
      (AddSubgroup.closure (Set.range b)).map e.toAddEquiv.toAddMonoidHom := by
    intro e
    rw [AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hper : ∀ (N : ℕ) (e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K),
      e.toLinearMap = (N : ℚ) • LinearMap.id → perSub K κ ι N =
      (AddSubgroup.closure (Set.range b)).map e.toAddEquiv.toAddMonoidHom := by
    intro N e he
    have he' : ∀ y, e y = (N : K) • y := fun y => by
      have := LinearMap.congr_fun he y
      rw [Nat.cast_smul_eq_nsmul] at this ⊢
      exact this
    ext x
    rw [mem_perSub_iff, AddSubgroup.mem_map]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, (hb y).2 hy, (he' y).trans h.symm⟩,
      fun ⟨y, hy, h⟩ => ⟨y, (hb y).1 hy, h.symm.trans (he' y)⟩⟩
  obtain ⟨e₁, h₁⟩ := hsc (R * M) (Nat.mul_pos hR hM)
  obtain ⟨e₂, h₂⟩ := hsc R hR
  rw [AddSubgroup.relIndex_eq_abs_det _ _ (map_perSub_le T R M hT) (b.map (e₁.trans T)) (b.map e₂)
    (by rw [hcl, hper _ _ h₁, AddSubgroup.map_map]; rfl) (by rw [hcl, hper _ _ h₂])]
  have hc : ⇑(b.map (e₁.trans T)) = ((M : ℚ) • T.toLinearMap) ∘ (b.map e₂) := by
    funext j
    have a₁ := LinearMap.congr_fun h₁ (b j)
    have a₂ := LinearMap.congr_fun h₂ (b j)
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at a₁ a₂
    simp [a₁, a₂, smul_smul, mul_comm]
  rw [hc, Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_smul, abs_mul,
    abs_of_nonneg (by positivity), ← Module.finrank_mul_finrank ℚ K (Matrix κ ι K),
    Module.finrank_matrix, Module.finrank_self, mul_one]

theorem periodic_of_level {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) :
    ∀ x, ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro x y hy
  obtain ⟨z, hz, rfl⟩ := (mem_perSub_iff _ _).1 hy
  exact h.2 x z hz

theorem haarAt_comp (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) (φ : Matrix κ ι K → ℂ) (h : HasLevel R φ) :
    haarAt (R * M) (fun x => φ (T x)) =
      ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haarAt R φ := by
  have hi := relIndex_map T R M hR hM hT
  have hle := map_perSub_le T R M hT
  have hd : LinearMap.det T.toLinearMap ≠ 0 := T.isUnit_det'.ne_zero
  have hne : ((perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom).relIndex
      (perSub K κ ι R) ≠ 0 := by
    intro h0
    rw [h0] at hi
    have : (0 : ℚ) < (M : ℚ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
        |LinearMap.det T.toLinearMap| := by positivity
    rw [← hi] at this
    simp at this
  have e1 := finsum_quot_map (perSub K κ ι (R * M)) T.toAddEquiv φ
    fun x y hy => periodic_of_level h x y (hle hy)
  have e2 := finsum_quot_le _ _ hle hne φ (periodic_of_level h)
  have hi' := congrArg (fun t : ℚ => (t : ℂ)) hi
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow] at hi'
  unfold haarAt
  erw [e1]
  rw [e2, hi']
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  rw [mul_pow]
  field_simp

theorem haarAt_mul (R M : ℕ) (hR : 0 < R) (hM : 0 < M) (φ : Matrix κ ι K → ℂ)
    (h : HasLevel R φ) : haarAt (R * M) φ = haarAt R φ := by
  simpa using haarAt_comp (LinearEquiv.refl ℚ _) R M hR hM (fun y hy => intM_nat_smul M hy) φ h

theorem haar_eq_haarAt {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) :
    haar φ = haarAt R φ := by
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dif_pos hs, ← haarAt_mul _ R hs.choose_spec.1 hR φ hs.choose_spec.2, mul_comm,
    haarAt_mul _ _ hR hs.choose_spec.1 φ h]

theorem haar_comp (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (T x)) ∧
      haar (fun x => φ (T x)) = ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haar φ := by
  obtain ⟨R, hR, h⟩ := hφ
  obtain ⟨M, hM, hT⟩ := exists_den T.toLinearMap
  obtain ⟨N, hN, hT'⟩ := exists_den T.symm.toLinearMap
  have hT2 : ∀ y, IntM y → IntM (((N * M : ℕ) : K) • T y) := fun y hy => by
    rw [Nat.cast_mul, mul_smul]
    exact intM_nat_smul N (hT y hy)
  have hl : HasLevel (R * (N * M)) (fun x => φ (T x)) := by
    refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
    · have := intM_nat_smul M (hT' _ (h.1 _ hx))
      rw [map_nat_smul] at this
      simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, smul_smul] at this
      convert this using 2
      push_cast; ring
    · have := h.2 (T x) _ (hT2 y hy)
      rw [smul_smul, ← Nat.cast_mul] at this
      simp only [map_add]
      rw [← this]
      congr 2
      exact map_nat_smul T.toLinearMap _ _
  have hp : 0 < R * (N * M) := by positivity
  refine ⟨⟨_, hp, hl⟩, ?_⟩
  rw [haar_eq_haarAt hp hl, haar_eq_haarAt hR h, haarAt_comp T R _ hR (by positivity) hT2 φ h]

theorem haar_comp_field (f : Matrix κ ι K →ₗ[K] Matrix κ ι K) (hf : LinearMap.det f ≠ 0)
    (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (f x)) ∧
      haar (fun x => φ (f x)) = ((|Algebra.norm ℚ (LinearMap.det f)| : ℚ) : ℂ) * haar φ := by
  have h := haar_comp ((f.equivOfDetNeZero hf).restrictScalars ℚ) φ hφ
  rw [← LinearMap.det_restrictScalars]
  exact h

theorem det_mul_right [DecidableEq ι] (A : Matrix ι ι K) :
    LinearMap.det (mulRightLinearMap κ K A) = A.det ^ Fintype.card κ := by
  have h := LinearMap.det_pi (fun _ : κ => Matrix.toLin' Aᵀ)
  rw [Finset.prod_const, LinearMap.det_toLin', Matrix.det_transpose, Finset.card_univ] at h
  rw [← h]
  congr 1
  refine LinearMap.ext fun x => ?_
  funext k i
  change (x * A) k i = (Aᵀ *ᵥ x k) i
  rw [Matrix.mulVec_transpose]
  rfl

theorem det_mul_left [DecidableEq κ] (A : Matrix κ κ K) :
    LinearMap.det (mulLeftLinearMap ι K A) = A.det ^ Fintype.card ι := by
  rw [← Matrix.det_transpose, ← det_mul_right, ← LinearMap.det_conj (mulRightLinearMap ι K Aᵀ)
    (Matrix.transposeLinearEquiv ι κ K K)]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp [Matrix.transpose_mul]

theorem haar_mul : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : Matrix κ ι K → ℂ), IsSB φ → (∀ A : Matrix ι ι K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (x * A)) ∧ haar (fun x : Matrix κ ι K => φ (x * A)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card κ * haar φ) ∧ ∀ A : Matrix κ κ K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (A * x)) ∧ haar (fun x : Matrix κ ι K => φ (A * x)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card ι * haar φ := by
  intro K κ ι _ _ _ _ _ _ φ hφ
  refine ⟨fun A hA => ?_, fun A hA => ?_⟩
  · have h := haar_comp_field (mulRightLinearMap κ K A)
      (by rw [det_mul_right]; exact pow_ne_zero _ hA) φ hφ
    rw [det_mul_right, map_pow, abs_pow, Rat.cast_pow] at h
    exact h
  · have h := haar_comp_field (mulLeftLinearMap ι K A)
      (by rw [det_mul_left]; exact pow_ne_zero _ hA) φ hφ
    rw [det_mul_left, map_pow, abs_pow, Rat.cast_pow] at h
    exact h

end GlobalTheory.SW.LinChange
