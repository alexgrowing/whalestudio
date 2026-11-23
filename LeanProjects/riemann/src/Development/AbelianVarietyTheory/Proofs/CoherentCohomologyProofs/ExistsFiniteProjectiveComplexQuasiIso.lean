import Mathlib

open CategoryTheory TensorProduct

universe u v w

namespace GlobalTheory

section Flat

variable {R : Type u} [CommRing R] {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D]

theorem flat_of_shortExact_of_flat_of_flat (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    [Module.Flat R B] [Module.Flat R C] : Module.Flat R A := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat g hg f hf h I
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype
    I.subtype_injective
  have h3 : (f.lTensor R) ∘ₗ (I.subtype.rTensor A) = (I.subtype.rTensor B) ∘ₗ (f.lTensor I) := by
    simp
  have h4 : Function.Injective ((f.lTensor R) ∘ₗ (I.subtype.rTensor A)) := by
    rw [h3]; exact h2.comp h1
  exact Function.Injective.of_comp (f := f.lTensor R) h4

theorem flat_prod [Module.Flat R A] [Module.Flat R B] : Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) I.subtype
    I.subtype_injective
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype
    I.subtype_injective
  have e : ∀ x, TensorProduct.prodRight R R R A B (I.subtype.rTensor (A × B) x) =
      Prod.map (I.subtype.rTensor A) (I.subtype.rTensor B)
        (TensorProduct.prodRight R R I A B x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; ext <;> simp
    | tmul m y => simp
    | add x y hx hy => simp only [map_add, hx, hy]; ext <;> simp
  intro x y hxy
  apply (TensorProduct.prodRight R R I A B).injective
  apply h1.prodMap h2
  rw [← e, ← e, hxy]

theorem exact_range_subtype_rangeRestrict {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.ker_rangeRestrict, h, Submodule.range_subtype]

theorem flat_range_of_exact {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g)
    [Module.Flat R B] [Module.Flat R (LinearMap.range g)] : Module.Flat R (LinearMap.range f) :=
  flat_of_shortExact_of_flat_of_flat _ _ (LinearMap.range f).subtype_injective
    g.surjective_rangeRestrict (exact_range_subtype_rangeRestrict h)

theorem lTensor_exact_of_flat_range {f : A →ₗ[R] B} {g : B →ₗ[R] C} {k : C →ₗ[R] D}
    (h : Function.Exact f g) (h' : Function.Exact g k) [Module.Flat R (LinearMap.range k)]
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat k.rangeRestrict
    k.surjective_rangeRestrict _ (LinearMap.range g).subtype_injective
    (exact_range_subtype_rangeRestrict h') M
  have h2 : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff] at h ⊢
    rw [LinearMap.ker_rangeRestrict, h]
  have h3 := lTensor_exact M h2 g.surjective_rangeRestrict
  have h4 : g.lTensor M = ((LinearMap.range g).subtype.lTensor M) ∘ₗ (g.rangeRestrict.lTensor M) := by
    rw [← LinearMap.lTensor_comp]; rfl
  rw [LinearMap.exact_iff] at h3 ⊢
  rw [h4, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 h1), h3]

theorem flat_range_of_exact_of_bounded {E : ℕ → Type*} [∀ p, AddCommGroup (E p)]
    [∀ p, Module R (E p)] [∀ p, Module.Flat R (E p)] (D : ∀ p, E p →ₗ[R] E (p + 1))
    (hD : ∀ p, Function.Exact (D p) (D (p + 1))) (n : ℕ) (hn : ∀ p, n < p → Subsingleton (E p))
    (p : ℕ) : Module.Flat R (LinearMap.range (D p)) := by
  have key : ∀ m p, n < p + 1 + m → Module.Flat R (LinearMap.range (D p)) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      have := hn (p + 1) hp
      infer_instance
    | succ m ih =>
      intro p hp
      have := ih (p + 1) (by omega)
      exact flat_range_of_exact (hD p)
  exact key n p (by omega)

end Flat

structure ConeExact {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
    [∀ p, AddCommGroup (C p)] (dK : ∀ p, K p → K (p + 1)) (dC : ∀ p, C p → C (p + 1))
    (φ : ∀ p, K p → C p) : Prop where
  inj : ∀ x : K 0, φ 0 x = 0 → dK 0 x = 0 → x = 0
  zero : ∀ (c : C 0) (k : K 1), dC 0 c = φ 1 k → dK 1 k = 0 → ∃ x : K 0, φ 0 x = c ∧ dK 0 x = k
  succ : ∀ (p : ℕ) (c : C (p + 1)) (k : K (p + 2)), dC (p + 1) c = φ (p + 2) k →
    dK (p + 2) k = 0 → ∃ (c' : C p) (k' : K (p + 1)),
      dC p c' + φ (p + 1) k' = c ∧ dK (p + 1) k' = k

theorem coneExact_id {K : ℕ → Type v} [∀ p, AddCommGroup (K p)] (d : ∀ p, K p →+ K (p + 1)) :
    ConeExact (fun p => d p) (fun p => d p) (fun _ x => x) :=
  ⟨fun _ h _ => h, fun c _ h _ => ⟨c, rfl, h⟩, fun p c _ h _ => ⟨0, c, by simp, h⟩⟩

section Cone

variable {R : Type u} [CommRing R] {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
  [∀ p, AddCommGroup (C p)] [∀ p, Module R (K p)] [∀ p, Module R (C p)]

def coneD (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (p : ℕ) : C p × K (p + 1) →ₗ[R] C (p + 1) × K (p + 2) :=
  ((dC p).coprod (-φ (p + 1))).prod (-(dK (p + 1)) ∘ₗ LinearMap.snd R _ _)

@[simp]
theorem coneD_apply (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (p : ℕ) (x : C p × K (p + 1)) :
    coneD dK dC φ p x = (dC p x.1 - φ (p + 1) x.2, - dK (p + 1) x.2) := by
  simp [coneD, sub_eq_add_neg]

variable {dK : ∀ p, K p →ₗ[R] K (p + 1)} {dC : ∀ p, C p →ₗ[R] C (p + 1)}
    {φ : ∀ p, K p →ₗ[R] C p}

theorem coneExact_iff (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) :
    ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p) ↔
      Function.Injective ((φ 0).prod (dK 0)) ∧
      Function.Exact ((φ 0).prod (dK 0)) (coneD dK dC φ 0) ∧
      ∀ p, Function.Exact (coneD dK dC φ p) (coneD dK dC φ (p + 1)) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, fun p => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      exact h0 x (congrArg Prod.fst hx) (congrArg Prod.snd hx)
    · rintro ⟨c, k⟩
      constructor
      · intro h
        simp only [coneD_apply, Prod.mk_eq_zero, sub_eq_zero, neg_eq_zero] at h
        obtain ⟨x, hx1, hx2⟩ := h1 c k h.1 h.2
        exact ⟨x, Prod.ext hx1 hx2⟩
      · rintro ⟨x, hx⟩
        rw [← hx]
        simp [hφ, hK]
    · rintro ⟨c, k⟩
      constructor
      · intro h
        simp only [coneD_apply, Prod.mk_eq_zero, sub_eq_zero, neg_eq_zero] at h
        obtain ⟨c', k', hx1, hx2⟩ := h2 p c k h.1 h.2
        refine ⟨(c', -k'), ?_⟩
        simp [hx1, hx2]
      · rintro ⟨x, hx⟩
        rw [← hx]
        simp [hφ, hK, hC]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun x hx hx' => ?_, fun c k h h' => ?_, fun p c k h h' => ?_⟩
    · exact (injective_iff_map_eq_zero _).1 h0 x (Prod.ext hx hx')
    · obtain ⟨x, hx⟩ := (h1 (c, k)).1 (by simp [h, h'])
      exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    · obtain ⟨⟨c', k'⟩, hx⟩ := (h2 p (c, k)).1 (by simp [h, h'])
      simp only [coneD_apply, Prod.mk.injEq] at hx
      exact ⟨c', -k', by simp [← hx.1, sub_eq_add_neg], by simp [← hx.2]⟩

theorem flat_range_coneD [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ∀ p, Function.Exact (coneD dK dC φ p) (coneD dK dC φ (p + 1))) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p)) (p : ℕ) :
    Module.Flat R (LinearMap.range (coneD dK dC φ p)) := by
  have : ∀ p, Module.Flat R (C p × K (p + 1)) := fun p => flat_prod
  refine flat_range_of_exact_of_bounded (E := fun p => C p × K (p + 1)) _ h n (fun p hp => ?_) p
  have := hnK (p + 1) (by omega)
  have := hnC p hp
  infer_instance

theorem ConeExact.flat_zero [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p)) :
    Module.Flat R (K 0) := by
  obtain ⟨h0, h1, h2⟩ := (coneExact_iff hK hC hφ).1 h
  have := flat_range_coneD h2 n hnK hnC 0
  have : Module.Flat R (C 0 × K (0 + 1)) := flat_prod
  have := flat_range_of_exact h1
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective _ h0)

theorem ConeExact.lTensor [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (fun p => (dK p).lTensor M) (fun p => (dC p).lTensor M)
      (fun p => (φ p).lTensor M) := by
  obtain ⟨h0, h1, h2⟩ := (coneExact_iff hK hC hφ).1 h
  have hfl := flat_range_coneD h2 n hnK hnC
  have e0 : ∀ x, ((φ 0).lTensor M).prod ((dK 0).lTensor M) x =
      TensorProduct.prodRight R R M _ _ (((φ 0).prod (dK 0)).lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have e1 : ∀ p x, coneD (fun p => (dK p).lTensor M) (fun p => (dC p).lTensor M)
      (fun p => (φ p).lTensor M) p (TensorProduct.prodRight R R M _ _ x) =
      TensorProduct.prodRight R R M _ _ ((coneD dK dC φ p).lTensor M x) := by
    intro p x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m y => simp [tmul_sub, tmul_neg]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine (coneExact_iff (fun p x => ?_) (fun p x => ?_) (fun p x => ?_)).2 ⟨?_, ?_, fun p => ?_⟩
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dK (p + 1) ∘ₗ dK p = 0 from LinearMap.ext (hK p)]
    simp
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dC (p + 1) ∘ₗ dC p = 0 from LinearMap.ext (hC p)]
    simp
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dC p ∘ₗ φ p = φ (p + 1) ∘ₗ dK p from LinearMap.ext (hφ p), LinearMap.lTensor_comp,
      LinearMap.comp_apply]
  · have := hfl 0
    have h3 : Function.Exact ((φ 0).prod (dK 0)) (coneD dK dC φ 0).rangeRestrict := by
      rw [LinearMap.exact_iff] at h1 ⊢
      rw [LinearMap.ker_rangeRestrict, h1]
    have h4 := LinearMap.lTensor_injective_of_exact_of_flat _
      (coneD dK dC φ 0).surjective_rangeRestrict _ h0 h3 M
    intro x y hxy
    rw [e0, e0] at hxy
    exact h4 ((TensorProduct.prodRight R R M _ _).injective hxy)
  · have := hfl 1
    have h3 := lTensor_exact_of_flat_range h1 (h2 0) M
    intro y
    obtain ⟨y, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective y
    rw [e1, LinearEquiv.map_eq_zero_iff, h3 y]
    simp only [Set.mem_range, e0, EmbeddingLike.apply_eq_iff_eq]
  · have := hfl (p + 2)
    have h3 := lTensor_exact_of_flat_range (h2 p) (h2 (p + 1)) M
    intro y
    obtain ⟨y, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective y
    rw [e1, LinearEquiv.map_eq_zero_iff, h3 y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, e1 p x⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective x
      rw [e1] at hx
      exact ⟨x, (TensorProduct.prodRight R R M _ _).injective hx⟩

end Cone

section Construction

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem exists_free_step {C₀ C₁ K₁ K₂ : Type*} [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup K₁] [AddCommGroup K₂] [Module R C₀] [Module R C₁] [Module R K₁] [Module R K₂]
    [Module.Finite R K₁] (d : C₀ →ₗ[R] C₁) (φ : K₁ →ₗ[R] C₁) (δ : K₁ →ₗ[R] K₂) (B : Submodule R C₀)
    [Module.Finite R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)] :
    ∃ (m : ℕ) (φ₀ : (Fin m → R) →ₗ[R] C₀) (δ₀ : (Fin m → R) →ₗ[R] K₁),
      (∀ x, d (φ₀ x) = φ (δ₀ x)) ∧ (∀ x, δ (δ₀ x) = 0) ∧
      ∀ c k, d c = φ k → δ k = 0 → ∃ x, c - φ₀ x ∈ B ∧ δ₀ x = k := by
  let N : Submodule R (C₀ × K₁) :=
    LinearMap.ker (d.coprod (-φ)) ⊓ LinearMap.ker (δ ∘ₗ LinearMap.snd R _ _)
  have hN : ∀ x, x ∈ N ↔ d x.1 = φ x.2 ∧ δ x.2 = 0 := by
    intro x
    simp [N, add_neg_eq_zero]
  let s : N →ₗ[R] K₁ := LinearMap.snd R _ _ ∘ₗ N.subtype
  obtain ⟨a, π₁, hπ₁⟩ := Module.Finite.exists_fin' R (LinearMap.range s)
  obtain ⟨g₁, hg₁⟩ := Module.projective_lifting_property s.rangeRestrict π₁
    s.surjective_rangeRestrict
  obtain ⟨b, π₂, hπ₂⟩ :=
    Module.Finite.exists_fin' R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)
  obtain ⟨g₂, hg₂⟩ := Module.projective_lifting_property
    (B.comap (LinearMap.ker d).subtype).mkQ π₂ (Submodule.mkQ_surjective _)
  let e : (Fin (a + b) → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
    (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)
  refine ⟨a + b, ((LinearMap.fst R _ _ ∘ₗ N.subtype ∘ₗ g₁).coprod
    ((LinearMap.ker d).subtype ∘ₗ g₂)) ∘ₗ e.toLinearMap,
    (s ∘ₗ g₁ ∘ₗ LinearMap.fst R _ _) ∘ₗ e.toLinearMap, fun x => ?_, fun x => ?_,
    fun c k h h' => ?_⟩
  · have h1 := ((hN _).1 (g₁ (e x).1).2).1
    have h2 : d (g₂ (e x).2) = 0 := (g₂ (e x).2).2
    simp [s, h1, h2]
  · exact ((hN _).1 (g₁ (e x).1).2).2
  · obtain ⟨x, hx⟩ := hπ₁ (s.rangeRestrict ⟨(c, k), (hN _).2 ⟨h, h'⟩⟩)
    have hx' : ((g₁ x : N) : C₀ × K₁).2 = k := by
      rw [← hg₁] at hx
      exact congrArg Subtype.val hx
    have h1 := ((hN _).1 (g₁ x).2).1
    have h3 : c - ((g₁ x : N) : C₀ × K₁).1 ∈ LinearMap.ker d := by
      simp [h, h1, hx']
    obtain ⟨y, hy⟩ := hπ₂ ((B.comap (LinearMap.ker d).subtype).mkQ ⟨_, h3⟩)
    rw [← hg₂] at hy
    have h4 := (Submodule.Quotient.eq _).1 hy.symm
    refine ⟨e.symm (x, y), ?_, ?_⟩
    · simpa [sub_sub] using h4
    · simpa [s] using hx'

theorem exists_free_complex (n : ℕ) : ∀ (C : ℕ → ModuleCat.{v} R)
    (d : ∀ p, C p →ₗ[R] C (p + 1)) (B : Submodule R (C 0))
    (_ : ∀ p, n ≤ p → Subsingleton (C p))
    (_ : Module.Finite R (LinearMap.ker (d 0) ⧸ B.comap (LinearMap.ker (d 0)).subtype))
    (_ : ∀ p, Module.Finite R (LinearMap.ker (d (p + 1)) ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)),
    ∃ (m : ℕ → ℕ) (δ : ∀ p, (Fin (m p) → R) →ₗ[R] (Fin (m (p + 1)) → R))
      (φ : ∀ p, (Fin (m p) → R) →ₗ[R] C p),
      (∀ p, n ≤ p → m p = 0) ∧ (∀ p x, δ (p + 1) (δ p x) = 0) ∧
      (∀ p x, d p (φ p x) = φ (p + 1) (δ p x)) ∧
      (∀ c k, d 0 c = φ 1 k → δ 1 k = 0 → ∃ x, c - φ 0 x ∈ B ∧ δ 0 x = k) ∧
      ∀ p c k, d (p + 1) c = φ (p + 2) k → δ (p + 2) k = 0 →
        ∃ c' k', d p c' + φ (p + 1) k' = c ∧ δ (p + 1) k' = k := by
  induction n with
  | zero =>
    intro C d B hC _ _
    have hC' : ∀ p, Subsingleton (C p) := fun p => hC p p.zero_le
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => Subsingleton.elim _ _, fun c k _ _ => ⟨0, ?_, Subsingleton.elim _ _⟩,
      fun p c k _ _ => ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    rw [Subsingleton.elim (c - _) 0]
    exact B.zero_mem
  | succ n ih =>
    intro C d B hC hB hH
    obtain ⟨m, δ, φ, hm, hδ, hφ, h0, h1⟩ := ih (fun p => C (p + 1)) (fun p => d (p + 1))
      (LinearMap.range (d 0)) (fun p hp => hC _ (by omega)) (hH 0) (fun p => hH (p + 1))
    obtain ⟨a, φ₀, δ₀, e1, e2, e3⟩ := exists_free_step (d 0) (φ 0) (δ 0) B
    refine ⟨fun p => Nat.casesOn p a m,
      fun p => match p with | 0 => δ₀ | p + 1 => δ p,
      fun p => match p with | 0 => φ₀ | p + 1 => φ p, ?_, ?_, ?_, e3, ?_⟩
    · rintro (_ | p) hp
      · omega
      · exact hm p (by omega)
    · rintro (_ | p)
      · exact e2
      · exact hδ p
    · rintro (_ | p)
      · exact e1
      · exact hφ p
    · rintro (_ | p)
      · intro c k h h'
        obtain ⟨x, ⟨c', hc'⟩, hx⟩ := h0 c k h h'
        exact ⟨c', x, eq_sub_iff_add_eq.1 hc', hx⟩
      · exact h1 p

end Construction

section QuasiIso

variable {R : Type u} [Ring R]

theorem shortComplex_quasiIso_iff {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 → ∃ (x : S.X₂) (z : T.X₁), S.g x = 0 ∧ T.f z + φ.τ₂ x = y) ∧
      (∀ (x : S.X₂) (z : T.X₁), S.g x = 0 → T.f z = φ.τ₂ x → ∃ w : S.X₁, S.f w = x) := by
  let γ := ShortComplex.leftHomologyMapData φ S.moduleCatLeftHomologyData
    T.moduleCatLeftHomologyData
  let φK : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom := γ.φK.hom
  let φH : (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[R]
    (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) := γ.φH.hom
  have hi : ∀ x, (φK x : T.X₂) = φ.τ₂ x := fun x => congr($(γ.commi).hom x)
  have hπ : ∀ x, φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φK x) :=
    fun x => congr($(γ.commπ).hom x)
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective φH ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
    · obtain ⟨x, hx⟩ := h2 (Submodule.Quotient.mk ⟨y, hy⟩)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ] at hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 hx.symm
      refine ⟨x, z, x.2, ?_⟩
      have : T.f z = y - φK x := congrArg Subtype.val hz
      rw [this, hi, sub_add_cancel]
    · have : φH (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
        rw [hπ, Submodule.Quotient.mk_eq_zero]
        exact ⟨z, Subtype.ext (hz.trans (hi ⟨x, hx⟩).symm)⟩
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1
        ((injective_iff_map_eq_zero _).1 h1 _ this)
      exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨z, hz⟩ := hx
      obtain ⟨w, hw⟩ := h2 x z x.2 ((congrArg Subtype.val hz).trans (hi x))
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, Subtype.ext hw⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨x, z, hx, hz⟩ := h1 y y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      rw [hπ]
      symm
      refine (Submodule.Quotient.eq _).2 ⟨z, Subtype.ext ?_⟩
      change T.f z = y - φK ⟨x, hx⟩
      rw [hi, ← hz, add_sub_cancel_right]

theorem cochain_d_d_apply (K : CochainComplex (ModuleCat.{v} R) ℕ) (i j k : ℕ) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := congr($(K.d_comp_d i j k).hom x)

theorem cochain_comm_apply {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (i j : ℕ)
    (x : K.X i) : (C.d i j).hom ((φ.f i).hom x) = (φ.f j).hom ((K.d i j).hom x) :=
  congr($(φ.comm i j).hom x)

theorem quasiIsoAt_zero_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIsoAt φ 0 ↔
      (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ x : K.X 0, (K.d 0 1).hom x = 0 ∧ (φ.f 0).hom x = y) ∧
      (∀ x : K.X 0, (K.d 0 1).hom x = 0 → (φ.f 0).hom x = 0 → x = 0) := by
  rw [quasiIsoAt_iff' φ 0 0 1 (by simp) (by simp), shortComplex_quasiIso_iff]
  have hK : ∀ x, (K.d 0 0).hom x = 0 := fun x => by rw [K.shape 0 0 (by simp)]; rfl
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  change (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 ∧
    (C.d 0 0).hom z + (φ.f 0).hom x = y) ∧ (∀ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 →
      (C.d 0 0).hom z = (φ.f 0).hom x → ∃ w : K.X 0, (K.d 0 0).hom w = x) ↔ _
  simp only [hK, hC, zero_add]
  refine and_congr (forall₂_congr fun y _ => ?_) ⟨fun h x h1 h2 => ?_, fun h x _ h1 h2 => ?_⟩
  · exact ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, 0, h⟩⟩
  · obtain ⟨_, hw⟩ := h x 0 h1 h2.symm
    exact hw.symm
  · exact ⟨0, (h x h1 h2.symm).symm⟩

theorem quasiIsoAt_succ_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (p : ℕ) :
    QuasiIsoAt φ (p + 1) ↔
      (∀ y : C.X (p + 1), (C.d (p + 1) (p + 2)).hom y = 0 →
        ∃ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 ∧
          (C.d p (p + 1)).hom z + (φ.f (p + 1)).hom x = y) ∧
      (∀ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 →
        (C.d p (p + 1)).hom z = (φ.f (p + 1)).hom x → ∃ w : K.X p, (K.d p (p + 1)).hom w = x) := by
  rw [quasiIsoAt_iff' φ p (p + 1) (p + 2) (by simp) (by simp), shortComplex_quasiIso_iff]
  rfl

theorem quasiIso_iff_coneExact {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIso φ ↔ ConeExact (K := fun p => K.X p) (C := fun p => C.X p)
      (fun p => (K.d p (p + 1)).hom) (fun p => (C.d p (p + 1)).hom) (fun p => (φ.f p).hom) := by
  rw [quasiIso_iff]
  constructor
  · intro h
    have h0 := (quasiIsoAt_zero_iff φ).1 (h 0)
    have h1 := fun p => (quasiIsoAt_succ_iff φ p).1 (h (p + 1))
    refine ⟨fun x hx hx' => h0.2 x hx' hx, fun c k hc hk => ?_, fun p c k hc hk => ?_⟩
    · obtain ⟨w, rfl⟩ := (h1 0).2 k c hk hc
      obtain ⟨x, hx, hx'⟩ := h0.1 (c - (φ.f 0).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨x + w, by rw [map_add, hx', sub_add_cancel], by rw [map_add, hx]; exact zero_add _⟩
    · obtain ⟨w, rfl⟩ := (h1 (p + 1)).2 k c hk hc
      obtain ⟨x, z, hx, hx'⟩ := (h1 p).1 (c - (φ.f (p + 1)).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨z, x + w, by rw [map_add, ← add_assoc, hx', sub_add_cancel],
        by rw [map_add, hx, zero_add]⟩
  · rintro ⟨h0, h1, h2⟩ (_ | p)
    · refine (quasiIsoAt_zero_iff φ).2 ⟨fun y hy => ?_, fun x hx hx' => h0 x hx' hx⟩
      obtain ⟨x, hx, hx'⟩ := h1 y 0 (by rw [map_zero]; exact hy) (map_zero _)
      exact ⟨x, hx', hx⟩
    · refine (quasiIsoAt_succ_iff φ p).2 ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
      · obtain ⟨z, x, hx, hx'⟩ := h2 p y 0 (by rw [map_zero]; exact hy) (map_zero _)
        exact ⟨x, z, hx', hx⟩
      · cases p with
        | zero =>
          obtain ⟨w, -, hw⟩ := h1 z x hz hx
          exact ⟨w, hw⟩
        | succ p =>
          obtain ⟨-, w, -, hw⟩ := h2 p z x hz hx
          exact ⟨w, hw⟩

end QuasiIso

section Main

open Limits

variable {R : Type u} [CommRing R]

theorem coneExact_lTensor_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (K := fun p => M ⊗[R] K.X p) (C := fun p => M ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (φ.f p).hom.lTensor M) :=
  ConeExact.lTensor (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp)) M

theorem quasiIso_tensorLeft_of_flat {K C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : ModuleCat.{u} R) :
    QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC M)

instance extendScalars_additive {S : Type w} [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, w, v} f).Additive where
  map_add {M N} g h := by
    letI := f.toAlgebra
    ext m
    exact tmul_add (R := R) (1 : S) (g.hom m) (h.hom m)

theorem quasiIso_extendScalars_of_flat {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    {S : Type w} [CommRing S] (f : R →+* S) :
    QuasiIso (((ModuleCat.extendScalars.{u, w, v} f).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))

theorem finite_ker_quotient_of_finite_homology (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    [Module.Finite R (C.homology j)] :
    Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
    LinearMap.range (C.sc' i j k).moduleCatToCycles) := Module.Finite.equiv e
  refine Module.Finite.equiv (Submodule.quotEquivOfEq
    (LinearMap.range (C.sc' i j k).moduleCatToCycles) _ ?_)
  ext x
  exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩

theorem exists_finite_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ QuasiIso φ := by
  obtain ⟨m, δ, ψ, hm, hδ, hψ, h0, h1⟩ := exists_free_complex (n + 1) C.X
    (fun p => (C.d p (p + 1)).hom) (LinearMap.range (C.d 0 0).hom)
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hn p hp))
    (finite_ker_quotient_of_finite_homology C 0 0 1 (by simp) (by simp))
    (fun p => finite_ker_quotient_of_finite_homology C p (p + 1) (p + 2) (by simp) (by simp))
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  let N := LinearMap.range ((ψ 0).prod (δ 0))
  let X : ℕ → ModuleCat.{u} R := fun p => match p with
    | 0 => ModuleCat.of R N
    | p + 1 => ModuleCat.of R (Fin (m (p + 1)) → R)
  let d : ∀ p, X p ⟶ X (p + 1) := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.snd R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (δ (p + 1))
  let f : ∀ p, X p ⟶ C.X p := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.fst R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (ψ (p + 1))
  have hd : ∀ p, d p ≫ d (p + 1) = 0 := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hδ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hδ (p + 1)))
  have hf : ∀ p, f p ≫ C.d p (p + 1) = d p ≫ f (p + 1) := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hψ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hψ (p + 1)))
  let K : CochainComplex (ModuleCat.{u} R) ℕ := CochainComplex.of X d hd
  have hKd : ∀ p, K.d p (p + 1) = d p := fun p => by simp [K, CochainComplex.of_d]
  let φ : K ⟶ C :=
    { f := f
      comm' := by
        rintro i _ rfl
        rw [hKd]
        exact hf i }
  refine ⟨K, φ, ?_, ?_, ?_, ?_⟩
  · rintro (_ | p) hp
    · omega
    · refine ModuleCat.isZero_iff_subsingleton.2 ?_
      change Subsingleton (Fin (m (p + 1)) → R)
      rw [hm _ hp]
      infer_instance
  · rintro (_ | p)
    · exact inferInstanceAs (Module.Finite R N)
    · exact inferInstanceAs (Module.Finite R (Fin (m (p + 1)) → R))
  · rintro (_ | p) hp
    · omega
    · exact inferInstanceAs (Module.Free R (Fin (m (p + 1)) → R))
  · rw [quasiIso_iff_coneExact]
    simp only [hKd]
    refine ⟨fun x hx hx' => Subtype.ext (Prod.ext hx hx'), fun c k h h' => ?_, h1⟩
    obtain ⟨x, ⟨y, hy⟩, hx⟩ := h0 c k h h'
    rw [hC] at hy
    exact ⟨⟨_, x, rfl⟩, (sub_eq_zero.1 hy.symm).symm, hx⟩

theorem flat_zero_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, 1 ≤ p → Module.Flat R (K.X p))
    (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p)) :
    Module.Flat R (K.X 0) :=
  haveI : ∀ p, Module.Flat R (K.X (p + 1)) := fun p => hK _ (Nat.le_add_left 1 p)
  ConeExact.flat_zero (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp))

theorem exists_finite_projective_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ (∀ p, Module.Projective R (K.X p)) ∧
      QuasiIso φ ∧
      (∀ M : ModuleCat.{u} R,
        QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ)) ∧
      (∀ (S : Type w) [CommRing S] [Algebra R S], QuasiIso
        (((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex _).map φ)) := by
  obtain ⟨K, φ, h1, h2, h3, h4⟩ := exists_finite_complex_quasiIso C n hn hfin
  have h5 : ∀ p, 1 ≤ p → Module.Flat R (K.X p) := fun p hp => by
    have := h3 p hp
    infer_instance
  have h6 : ∀ p, Module.Flat R (K.X p) := by
    rintro (_ | p)
    · exact flat_zero_of_quasiIso φ h5 hflat n h1 hn
    · exact h5 _ (Nat.le_add_left 1 p)
  refine ⟨K, φ, h1, h2, h3, fun p => ?_, h4,
    quasiIso_tensorLeft_of_flat φ h6 hflat n h1 hn,
    fun S _ _ => quasiIso_extendScalars_of_flat φ h6 hflat n h1 hn _⟩
  have := Module.finitePresentation_of_finite R (K.X p)
  exact Module.Flat.projective_of_finitePresentation

end Main

end GlobalTheory
