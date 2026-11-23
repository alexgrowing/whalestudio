import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

noncomputable section

namespace GlobalTheory.UnitLemma.ProdCount

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

theorem finsum_prod_mul {α β : Type} (f : α → ℚ) (g : β → ℚ) :
    ∑ᶠ p : α × β, f p.1 * g p.2 = (∑ᶠ a, f a) * ∑ᶠ b, g b := by
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hf0
  obtain ⟨b0, hb0⟩ := Function.ne_iff.1 hg0
  have hs : Function.support (fun p : α × β => f p.1 * g p.2) = Function.support f ×ˢ Function.support g := by
    ext p
    simp [Function.mem_support]
  by_cases hf : (Function.support f).Finite
  · by_cases hg : (Function.support g).Finite
    · rw [finsum_eq_sum_of_support_subset (s := hf.toFinset) f (by simp),
        finsum_eq_sum_of_support_subset (s := hg.toFinset) g (by simp),
        finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ hg.toFinset) _ (by rw [hs]; simp),
        Finset.sum_mul_sum, Finset.sum_product]
    · rw [finsum_of_infinite_support hg, mul_zero, finsum_of_infinite_support]
      rw [hs]
      exact Set.Infinite.prod_right hg ⟨a0, ha0⟩
  · rw [finsum_of_infinite_support hf, zero_mul, finsum_of_infinite_support]
    rw [hs]
    exact Set.Infinite.prod_left hf ⟨b0, hb0⟩

theorem relIndex_prod' {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by
  have h : (H₁.prod H₂).subgroupOf (K₁.prod K₂) =
      ((H₁.subgroupOf K₁).prod (H₂.subgroupOf K₂)).comap (K₁.prodEquiv K₂).toMonoidHom := by
    ext x
    rfl
  unfold Subgroup.relIndex
  rw [h, Subgroup.index_comap_of_surjective _ (K₁.prodEquiv K₂).surjective, Subgroup.index_prod]

section General

variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]

theorem mulLat_prod (t : A₁ × A₂) (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    mulLat O t (L₁.prod L₂) = (mulLat O t.1 L₁).prod (mulLat O t.2 L₂) := by
  ext y
  simp only [mulLat, Submodule.mem_map, Submodule.mem_prod, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨z.1, h1, rfl⟩, ⟨z.2, h2, rfl⟩⟩
  · rintro ⟨⟨a, ha, e1⟩, ⟨b, hb, e2⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext e1 e2⟩

theorem mulLat_one (L : Submodule O A₁) : mulLat O (1 : A₁) L = L := by
  ext y
  simp [mulLat]

theorem isIntegral_prod_iff (t : A₁ × A₂) : IsIntegral O t ↔ IsIntegral O t.1 ∧ IsIntegral O t.2 :=
  ⟨fun h => ⟨h.map (AlgHom.fst O A₁ A₂), h.map (AlgHom.snd O A₁ A₂)⟩, fun h => IsIntegral.pair h.1 h.2⟩

theorem stabLat_prod (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) (t : (A₁ × A₂)ˣ) :
    t ∈ stabLat O (L₁.prod L₂) ↔
      (MulEquiv.prodUnits t).1 ∈ stabLat O L₁ ∧ (MulEquiv.prodUnits t).2 ∈ stabLat O L₂ := by
  change (∀ y, y ∈ L₁.prod L₂ ↔ (t : A₁ × A₂) * y ∈ L₁.prod L₂) ↔
    (∀ y, y ∈ L₁ ↔ (t : A₁ × A₂).1 * y ∈ L₁) ∧ (∀ y, y ∈ L₂ ↔ (t : A₁ × A₂).2 * y ∈ L₂)
  simp only [Submodule.mem_prod, Prod.fst_mul, Prod.snd_mul]
  constructor
  · intro h
    exact ⟨fun y => by simpa using h (y, 0), fun y => by simpa using h (0, y)⟩
  · rintro ⟨h1, h2⟩ y
    rw [← h1, ← h2]

theorem intUnits_prod (t : (A₁ × A₂)ˣ) :
    t ∈ intUnits O (A₁ × A₂) ↔
      (MulEquiv.prodUnits t).1 ∈ intUnits O A₁ ∧ (MulEquiv.prodUnits t).2 ∈ intUnits O A₂ := by
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [isIntegral_prod_iff, isIntegral_prod_iff]
  tauto

theorem orbSum_prod (G₁ : Subgroup A₁ˣ) (G₂ : Subgroup A₂ˣ) (G : Subgroup (A₁ × A₂)ˣ)
    (hG : ∀ t, t ∈ G ↔ (MulEquiv.prodUnits t).1 ∈ G₁ ∧ (MulEquiv.prodUnits t).2 ∈ G₂)
    (X₁ : Set (Submodule O A₁)) (X₂ : Set (Submodule O A₂)) (X : Set (Submodule O (A₁ × A₂)))
    (hX : ∀ L₁ L₂, Submodule.prod L₁ L₂ ∈ X ↔ L₁ ∈ X₁ ∧ L₂ ∈ X₂)
    (hsplit : ∀ L ∈ X, ∃ L₁ L₂, L = Submodule.prod L₁ L₂) :
    orbSum O G X (fun _ => 1) = orbSum O G₁ X₁ (fun _ => 1) * orbSum O G₂ X₂ (fun _ => 1) := by
  rw [orbSum_eq, orbSum_eq, orbSum_eq, ← finsum_prod_mul]
  let f : X₁ → X₂ → X := fun L₁ L₂ => ⟨L₁.1.prod L₂.1, (hX _ _).2 ⟨L₁.2, L₂.2⟩⟩
  have key : ∀ (t₁ : A₁ˣ) (t₂ : A₂ˣ), t₁ ∈ G₁ → t₂ ∈ G₂ → ∀ (L₁ M₁ : X₁) (L₂ M₂ : X₂),
      M₁.1 = mulLat O (t₁ : A₁) L₁.1 → M₂.1 = mulLat O (t₂ : A₂) L₂.1 →
      ∃ t ∈ G, (f M₁ M₂).1 = mulLat O ((t : (A₁ × A₂)ˣ) : A₁ × A₂) (f L₁ L₂).1 := by
    intro t₁ t₂ h₁ h₂ L₁ M₁ L₂ M₂ e₁ e₂
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), by rw [hG]; simpa using ⟨h₁, h₂⟩, ?_⟩
    change M₁.1.prod M₂.1 = mulLat O ((t₁ : A₁), (t₂ : A₂)) (L₁.1.prod L₂.1)
    rw [mulLat_prod, e₁, e₂]
  let F : Orb O G₁ X₁ → Orb O G₂ X₂ → Orb O G X := Quot.map₂ f
    (by
      rintro L₁ L₂ M₂ ⟨t, ht, e⟩
      exact key 1 t G₁.one_mem ht L₁ L₁ L₂ M₂ (mulLat_one _).symm e)
    (by
      rintro L₁ M₁ L₂ ⟨t, ht, e⟩
      exact key t 1 ht G₂.one_mem L₁ M₁ L₂ L₂ e (mulLat_one _).symm)
  have hsurj : ∀ L : X, ∃ L₁ L₂, L = f L₁ L₂ := by
    rintro ⟨L, hL⟩
    obtain ⟨L₁, L₂, rfl⟩ := hsplit L hL
    exact ⟨⟨L₁, ((hX _ _).1 hL).1⟩, ⟨L₂, ((hX _ _).1 hL).2⟩, rfl⟩
  let p₁ : X → X₁ := fun L => ⟨L.1.map (LinearMap.fst O A₁ A₂), by
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    simpa [f] using L₁.2⟩
  let p₂ : X → X₂ := fun L => ⟨L.1.map (LinearMap.snd O A₁ A₂), by
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    simpa [f] using L₂.2⟩
  have hp₁ : ∀ L₁ L₂, p₁ (f L₁ L₂) = L₁ := fun L₁ L₂ => Subtype.ext (by simp [p₁, f])
  have hp₂ : ∀ L₁ L₂, p₂ (f L₁ L₂) = L₂ := fun L₁ L₂ => Subtype.ext (by simp [p₂, f])
  have key2 : ∀ L M : X, (∃ t ∈ G, M.1 = mulLat O ((t : (A₁ × A₂)ˣ) : A₁ × A₂) L.1) →
      (∃ t ∈ G₁, (p₁ M).1 = mulLat O ((t : A₁ˣ) : A₁) (p₁ L).1) ∧
      (∃ t ∈ G₂, (p₂ M).1 = mulLat O ((t : A₂ˣ) : A₂) (p₂ L).1) := by
    rintro L M ⟨t, ht, e⟩
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    obtain ⟨M₁, M₂, rfl⟩ := hsurj M
    rw [hp₁, hp₁, hp₂, hp₂]
    change M₁.1.prod M₂.1 = mulLat O _ (L₁.1.prod L₂.1) at e
    rw [mulLat_prod] at e
    have e1 := congrArg (Submodule.map (LinearMap.fst O A₁ A₂)) e
    have e2 := congrArg (Submodule.map (LinearMap.snd O A₁ A₂)) e
    simp only [Submodule.prod_map_fst, Submodule.prod_map_snd] at e1 e2
    exact ⟨⟨_, ((hG t).1 ht).1, e1⟩, ⟨_, ((hG t).1 ht).2, e2⟩⟩
  let q : Orb O G₁ X₁ × Orb O G₂ X₂ ≃ Orb O G X :=
    { toFun := fun o => F o.1 o.2
      invFun := fun o => (Quot.map p₁ (fun L M h => (key2 L M h).1) o, Quot.map p₂ (fun L M h => (key2 L M h).2) o)
      left_inv := by
        rintro ⟨⟨L₁⟩, ⟨L₂⟩⟩
        change (Quot.mk _ (p₁ (f L₁ L₂)), Quot.mk _ (p₂ (f L₁ L₂))) = _
        rw [hp₁, hp₂]
        rfl
      right_inv := by
        rintro ⟨L⟩
        obtain ⟨L₁, L₂, rfl⟩ := hsurj L
        change Quot.mk _ (f (p₁ (f L₁ L₂)) (p₂ (f L₁ L₂))) = _
        rw [hp₁, hp₂] }
  rw [← finsum_comp_equiv q]
  refine finsum_congr ?_
  rintro ⟨⟨L₁⟩, ⟨L₂⟩⟩
  change (((stabLat O (L₁.1.prod L₂.1) ⊓ G).relIndex (intUnits O (A₁ × A₂) ⊓ G) : ℕ) : ℚ) =
    (((stabLat O L₁.1 ⊓ G₁).relIndex (intUnits O A₁ ⊓ G₁) : ℕ) : ℚ) *
    (((stabLat O L₂.1 ⊓ G₂).relIndex (intUnits O A₂ ⊓ G₂) : ℕ) : ℚ)
  have h1 : stabLat O (L₁.1.prod L₂.1) ⊓ G = ((stabLat O L₁.1 ⊓ G₁).prod (stabLat O L₂.1 ⊓ G₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
    ext t
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_prod, stabLat_prod, hG,
      MulEquiv.coe_toMonoidHom]
    tauto
  have h2 : intUnits O (A₁ × A₂) ⊓ G = ((intUnits O A₁ ⊓ G₁).prod (intUnits O A₂ ⊓ G₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
    ext t
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_prod, intUnits_prod, hG,
      MulEquiv.coe_toMonoidHom]
    tauto
  rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod', Nat.cast_mul]

theorem split_of_stable (g : A₁ × A₂) (he : ((1, 0) : A₁ × A₂) ∈ Algebra.adjoin O ({g} : Set (A₁ × A₂)))
    (L : Submodule O (A₁ × A₂)) (hL : ∀ y ∈ L, g * y ∈ L) : ∃ L₁ L₂, L = Submodule.prod L₁ L₂ := by
  have hall : ∀ u ∈ Algebra.adjoin O ({g} : Set (A₁ × A₂)), ∀ y ∈ L, u * y ∈ L := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hL
    | algebraMap a => intro y hy; rw [← Algebra.smul_def]; exact L.smul_mem a hy
    | add a b _ _ ha hb => intro y hy; rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb y hy)
  refine ⟨L.comap (LinearMap.inl O A₁ A₂), L.comap (LinearMap.inr O A₁ A₂), ?_⟩
  ext ⟨a, b⟩
  simp only [Submodule.mem_prod, Submodule.mem_comap, LinearMap.inl_apply, LinearMap.inr_apply]
  constructor
  · intro h
    have h1 : ((a, 0) : A₁ × A₂) ∈ L := by simpa using hall _ he _ h
    exact ⟨h1, by simpa using L.sub_mem h h1⟩
  · rintro ⟨h1, h2⟩
    simpa using L.add_mem h1 h2

theorem isLat_prod (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂] (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    IsLat O E (L₁.prod L₂) ↔ IsLat O E L₁ ∧ IsLat O E L₂ := by
  have hs : Submodule.span E ((L₁.prod L₂ : Submodule O (A₁ × A₂)) : Set (A₁ × A₂)) =
      (Submodule.span E (L₁ : Set A₁)).prod (Submodule.span E (L₂ : Set A₂)) := by
    rw [Submodule.prod_coe]
    exact Submodule.span_prod_eq E L₁.zero_mem L₂.zero_mem
  unfold IsLat
  rw [hs, Submodule.prod_eq_top_iff]
  constructor
  · rintro ⟨h, h1, h2⟩
    have a := h.map (LinearMap.fst O A₁ A₂)
    have b := h.map (LinearMap.snd O A₁ A₂)
    rw [Submodule.prod_map_fst] at a
    rw [Submodule.prod_map_snd] at b
    exact ⟨⟨a, h1⟩, b, h2⟩
  · rintro ⟨⟨a, h1⟩, b, h2⟩
    exact ⟨a.prod b, h1, h2⟩

end General

variable {K : UQ}

theorem herm_prod (B₁ B₂ : InvAlg K) (x y z : B₁.A × B₂.A) :
    (B₁.prod B₂).herm x y z = B₁.herm x.1 y.1 z.1 + B₂.herm x.2 y.2 z.2 :=
  Algebra.trace_prod_apply (R := K.E) (S := B₁.A) (T := B₂.A) _

theorem mem_X_prod (B₁ B₂ : InvAlg K) (x₁ : B₁.A) (x₂ : B₂.A) (L₁ : Submodule K.O B₁.A)
    (L₂ : Submodule K.O B₂.A) :
    L₁.prod L₂ ∈ (B₁.prod B₂).X (x₁, x₂) ↔ L₁ ∈ B₁.X x₁ ∧ L₂ ∈ B₂.X x₂ := by
  have z₁ : ∀ y, B₁.herm x₁ y 0 = 0 := fun y => by simp [InvAlg.herm]
  have z₂ : ∀ y, B₂.herm x₂ y 0 = 0 := fun y => by simp [InvAlg.herm]
  have w₁ : ∀ y, B₁.herm x₁ 0 y = 0 := fun y => by simp [InvAlg.herm]
  have w₂ : ∀ y, B₂.herm x₂ 0 y = 0 := fun y => by simp [InvAlg.herm]
  have hd : ∀ y : B₁.A × B₂.A,
      (∀ z : B₁.A × B₂.A, z ∈ L₁.prod L₂ → (B₁.prod B₂).herm (x₁, x₂) y z ∈ (algebraMap K.O K.E).range) ↔
      (∀ z ∈ L₁, B₁.herm x₁ y.1 z ∈ (algebraMap K.O K.E).range) ∧
      (∀ z ∈ L₂, B₂.herm x₂ y.2 z ∈ (algebraMap K.O K.E).range) := by
    intro y
    simp only [herm_prod, Submodule.mem_prod]
    constructor
    · intro h
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · have := h (z, 0) ⟨hz, L₂.zero_mem⟩
        rwa [z₂, add_zero] at this
      · have := h (0, z) ⟨L₁.zero_mem, hz⟩
        rwa [z₁, zero_add] at this
    · rintro ⟨h1, h2⟩ z hz
      exact add_mem (h1 _ hz.1) (h2 _ hz.2)
  change (IsLat K.O K.E (L₁.prod L₂) ∧
      (∀ y : B₁.A × B₂.A, y ∈ L₁.prod L₂ → ((B₁.g, B₂.g) : B₁.A × B₂.A) * y ∈ L₁.prod L₂) ∧
      ∀ y : B₁.A × B₂.A, y ∈ L₁.prod L₂ ↔ ∀ z : B₁.A × B₂.A, z ∈ L₁.prod L₂ →
        (B₁.prod B₂).herm (x₁, x₂) y z ∈ (algebraMap K.O K.E).range) ↔
    (IsLat K.O K.E L₁ ∧ (∀ y ∈ L₁, B₁.g * y ∈ L₁) ∧
      ∀ y, y ∈ L₁ ↔ ∀ z ∈ L₁, B₁.herm x₁ y z ∈ (algebraMap K.O K.E).range) ∧
    (IsLat K.O K.E L₂ ∧ (∀ y ∈ L₂, B₂.g * y ∈ L₂) ∧
      ∀ y, y ∈ L₂ ↔ ∀ z ∈ L₂, B₂.herm x₂ y z ∈ (algebraMap K.O K.E).range)
  rw [isLat_prod]
  simp only [hd]
  simp only [Submodule.mem_prod, Prod.fst_mul, Prod.snd_mul]
  constructor
  · rintro ⟨⟨l1, l2⟩, s, d⟩
    refine ⟨⟨l1, fun y hy => (s (y, 0) ⟨hy, L₂.zero_mem⟩).1, fun y => ?_⟩,
      ⟨l2, fun y hy => (s (0, y) ⟨L₁.zero_mem, hy⟩).2, fun y => ?_⟩⟩
    · have := d (y, 0)
      simpa only [L₂.zero_mem, w₂, zero_mem, implies_true, and_true] using this
    · have := d (0, y)
      simpa only [L₁.zero_mem, w₁, zero_mem, implies_true, true_and] using this
  · rintro ⟨⟨l1, s1, d1⟩, l2, s2, d2⟩
    exact ⟨⟨l1, l2⟩, fun y hy => ⟨s1 _ hy.1, s2 _ hy.2⟩, fun y => and_congr (d1 _) (d2 _)⟩

theorem N_prod_of_idem (B₁ B₂ : InvAlg K)
    (he : ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)))
    (x₁ : B₁.A) (x₂ : B₂.A) : (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  refine orbSum_prod (A₁ := B₁.A) (A₂ := B₂.A) B₁.T B₂.T (B₁.prod B₂).T (fun t => ?_) _ _ _
    (mem_X_prod B₁ B₂ x₁ x₂) (fun L hL => split_of_stable _ he L hL.2.1)
  exact Prod.ext_iff

theorem N_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ :=
  fun _ B₁ B₂ he _ x₁ x₂ _ _ _ _ => N_prod_of_idem B₁ B₂ he x₁ x₂

end GlobalTheory.UnitLemma.ProdCount
