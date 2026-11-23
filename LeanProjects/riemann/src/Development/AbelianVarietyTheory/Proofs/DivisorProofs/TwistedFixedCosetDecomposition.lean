import Mathlib
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwLangAb

theorem finite_nsmul_preimage {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (r : ℕ) (hr : 0 < r)
    (T : Set A) (hT : T.Finite) : {a : A | r • a ∈ T}.Finite := by
  let K : AddSubgroup A := (nsmulAddMonoidHom r : A →+ A).ker
  have h0 : Module.Finite ℤ (AddSubgroup.toIntSubmodule K) := inferInstance
  have h1 : Module.Finite ℤ K := h0
  have h2 : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp h1
  have hKf : Finite K := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨r, hr, ?_⟩
    apply Subtype.ext
    have hx : (nsmulAddMonoidHom r : A →+ A) (x : A) = 0 := AddMonoidHom.mem_ker.mp x.2
    simpa using hx
  have hKs : (K : Set A).Finite := Set.finite_coe_iff.mp hKf
  change ((fun a : A => r • a) ⁻¹' T).Finite
  refine hT.preimage' fun b _ => ?_
  by_cases hb : ∃ a0 : A, r • a0 = b
  · obtain ⟨a0, rfl⟩ := hb
    refine (hKs.image (fun k => a0 + k)).subset ?_
    intro a ha
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
    refine ⟨a - a0, ?_, by simp⟩
    show a - a0 ∈ K
    simp [K, smul_sub, ha]
  · have : (fun a : A => r • a) ⁻¹' {b} = ∅ := by
      ext a; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hb ⟨a, h⟩
    rw [this]; exact Set.finite_empty

theorem finite_pow_preimage {Q : Type*} [CommGroup Q] [Group.FG Q] (r : ℕ) (hr : 0 < r)
    (T : Set Q) (hT : T.Finite) : {x : Q | x ^ r ∈ T}.Finite := by
  haveI : AddGroup.FG (Additive Q) := inferInstance
  haveI : Module.Finite ℤ (Additive Q) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := finite_nsmul_preimage (A := Additive Q) r hr (Additive.toMul ⁻¹' T)
    (hT.preimage Additive.toMul.injective.injOn)
  refine (h.preimage (f := Additive.ofMul) Additive.ofMul.injective.injOn).subset ?_
  intro x hx
  simpa using hx

def fixedSubgroup {M : Type*} [Group M] (τ : M →* M) : Subgroup M where
  carrier := {x | τ x = x}
  one_mem' := map_one τ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem iterate_eq_mul_prod {M : Type*} [CommGroup M] (τ : M →* M) (t : M) (i : ℕ) :
    (⇑τ)^[i] t = t * ∏ j ∈ Finset.range i, (⇑τ)^[j] (t⁻¹ * τ t) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc (⇑τ)^[i + 1] t = (⇑τ)^[i] (τ t) := Function.iterate_succ_apply _ _ _
      _ = (⇑τ)^[i] (t * (t⁻¹ * τ t)) := by rw [mul_inv_cancel_left]
      _ = _ := by rw [iterate_map_mul, ih, Finset.prod_range_succ, mul_assoc]

theorem core {M : Type*} [CommGroup M] (τ : M →* M) (r : ℕ) (hr : 0 < r) (hτr : ∀ z, (⇑τ)^[r] z = z)
    (U : Subgroup M) (hU : ∀ u ∈ U, τ u ∈ U) (G : Set M) (hG : G.Finite)
    (hgen : ∀ z : M, z ∈ Subgroup.closure (G ∪ (U : Set M))) (F : Set M) (hF : F.Finite) :
    ∃ S : Finset M, ∀ t : M, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  let B := fixedSubgroup τ
  let K : Subgroup M := U ⊔ B
  let π : M →* M ⧸ K := QuotientGroup.mk' K
  have hUK : U ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  haveI : Group.FG (M ⧸ K) := by
    refine Group.fg_iff.2 ⟨π '' G, ?_, hG.image _⟩
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine Subgroup.closure_induction (p := fun x _ => π x ∈ Subgroup.closure (π '' G)) ?_ ?_ ?_ ?_ (hgen z)
    · intro x hx
      rcases hx with hx | hx
      · exact Subgroup.subset_closure ⟨x, hx, rfl⟩
      · have : π x = 1 := (QuotientGroup.eq_one_iff x).2 (hUK hx)
        rw [this]; exact one_mem _
    · rw [map_one]; exact one_mem _
    · intro x y _ _ hx hy
      rw [map_mul]; exact mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact inv_mem hx
  let P : M → M := fun c => ∏ i ∈ Finset.range r, ∏ j ∈ Finset.range i, (⇑τ)^[j] c
  have hPmul : ∀ a b, P (a * b) = P a * P b := by
    intro a b
    simp only [P, iterate_map_mul, Finset.prod_mul_distrib]
  have hit : ∀ j : ℕ, ∀ u ∈ U, (⇑τ)^[j] u ∈ U := by
    intro j
    induction j with
    | zero => intro u hu; exact hu
    | succ j ih => intro u hu; rw [Function.iterate_succ_apply']; exact hU _ (ih u hu)
  have hPU : ∀ u ∈ U, P u ∈ U := by
    intro u hu
    exact Subgroup.prod_mem _ fun i _ => Subgroup.prod_mem _ fun j _ => hit j u hu
  have key : ∀ t : M, π t ^ r = (π (P (t⁻¹ * τ t)))⁻¹ := by
    intro t
    let N := ∏ i ∈ Finset.range r, (⇑τ)^[i] t
    have hN : τ N = N := by
      have e1 : τ N = ∏ i ∈ Finset.range r, (⇑τ)^[i + 1] t := by
        simp only [N, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Function.iterate_succ_apply']
      have e2 := Finset.prod_range_succ (fun i => (⇑τ)^[i] t) r
      have e3 := Finset.prod_range_succ' (fun i => (⇑τ)^[i] t) r
      rw [hτr t] at e2
      rw [Function.iterate_zero_apply] at e3
      rw [e1]
      have := e3.symm.trans e2
      exact mul_right_cancel this
    have hNe : N = t ^ r * P (t⁻¹ * τ t) := by
      simp only [N, P]
      rw [Finset.prod_congr rfl fun i _ => iterate_eq_mul_prod τ t i, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    have hNK : π N = 1 := (QuotientGroup.eq_one_iff N).2 (hBK hN)
    rw [hNe, map_mul, map_pow] at hNK
    exact eq_inv_of_mul_eq_one_left hNK
  let T : Set (M ⧸ K) := (fun f => (π (P f))⁻¹) '' F
  have hX : {x : M ⧸ K | x ^ r ∈ T}.Finite := finite_pow_preimage r hr T (hF.image _)
  let σ := Function.surjInv (QuotientGroup.mk'_surjective K)
  refine ⟨hX.toFinset.image σ, ?_⟩
  rintro t ⟨f, hf, u, hu, hc⟩
  have hxT : π t ∈ {x : M ⧸ K | x ^ r ∈ T} := by
    show π t ^ r ∈ T
    refine ⟨f, hf, ?_⟩
    have h1 : π (P u) = 1 := (QuotientGroup.eq_one_iff _).2 (hUK (hPU u hu))
    show (π (P f))⁻¹ = π t ^ r
    rw [key t, hc, hPmul, map_mul, h1, mul_one]
  have hs : π (σ (π t)) = π t := Function.surjInv_eq _ _
  have hmem : (σ (π t))⁻¹ * t ∈ K := QuotientGroup.eq.mp hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨z, hz, σ (π t), Finset.mem_image.2 ⟨π t, hX.mem_toFinset.2 hxT, rfl⟩, y, hy, ?_⟩
  have e : σ (π t) * (y * z) = t := by rw [hyz, mul_inv_cancel_left]
  calc t = σ (π t) * (y * z) := e.symm
    _ = z * σ (π t) * y := by ac_rfl

theorem exists_finite_reps_of_twisted_lang : ∀ {H : Type} [Group H] (Z U : Subgroup H) (τ : H →* H) (r : ℕ),
    0 < r → (∀ z ∈ Z, τ z ∈ Z) →
    (∀ z ∈ Z, (⇑τ)^[r] z = z) → (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → U ≤ Z → (∀ u ∈ U, τ u ∈ U) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) →
    ∀ F : Finset H, ∃ S : Finset H, ∀ t ∈ Z, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b ∈ Z, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  intro H _ Z U τ r hr hτZ hτr hcomm hUZ hU hGex F
  obtain ⟨G, hGZ, hcl⟩ := hGex
  letI : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let τ' : Z →* Z :=
    { toFun := fun z => ⟨τ z, hτZ z z.2⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : H) (b : H)) }
  have hiter : ∀ (n : ℕ) (z : Z), (((⇑τ')^[n] z : Z) : H) = (⇑τ)^[n] (z : H) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let U' : Subgroup Z := U.subgroupOf Z
  let G' : Set Z := Subtype.val ⁻¹' (G : Set H)
  have hG' : G'.Finite := G.finite_toSet.preimage Subtype.val_injective.injOn
  have hle : Subgroup.closure ((G : Set H) ∪ (U : Set H)) ≤ Z :=
    (Subgroup.closure_le _).2 (Set.union_subset (fun g hg => hGZ g hg) hUZ)
  have hgen : ∀ z : Z, z ∈ Subgroup.closure (G' ∪ (U' : Set Z)) := by
    intro z
    have := Subgroup.closure_induction
      (p := fun x hx => (⟨x, hle hx⟩ : Z) ∈ Subgroup.closure (G' ∪ (U' : Set Z)))
      (fun x hx => by
        apply Subgroup.subset_closure
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Subgroup.mem_subgroupOf.2 hx))
      (one_mem _)
      (fun x y _ _ hx hy => mul_mem hx hy)
      (fun x _ hx => inv_mem hx) (hcl z.2)
    simpa using this
  let F' : Set Z := Subtype.val ⁻¹' (F : Set H)
  have hF' : F'.Finite := F.finite_toSet.preimage Subtype.val_injective.injOn
  obtain ⟨S', hS'⟩ := core τ' r hr (fun z => Subtype.ext (by rw [hiter]; exact hτr (z : H) z.2)) U'
    (fun u hu => Subgroup.mem_subgroupOf.2 (hU _ (Subgroup.mem_subgroupOf.1 hu))) G' hG' hgen F' hF'
  refine ⟨S'.image Subtype.val, ?_⟩
  rintro t ht ⟨f, hf, u, hu, hc⟩
  have hfe : f = t⁻¹ * τ t * u⁻¹ := by rw [hc, mul_inv_cancel_right]
  have hfZ : f ∈ Z := by
    rw [hfe]
    exact mul_mem (mul_mem (inv_mem ht) (hτZ t ht)) (inv_mem (hUZ hu))
  obtain ⟨b, hb, s, hs, u', hu', he⟩ := hS' ⟨t, ht⟩
    ⟨⟨f, hfZ⟩, hf, ⟨u, hUZ hu⟩, Subgroup.mem_subgroupOf.2 hu, Subtype.ext hc⟩
  exact ⟨b, b.2, congrArg Subtype.val hb, s, Finset.mem_image_of_mem _ hs, u',
    Subgroup.mem_subgroupOf.1 hu', congrArg Subtype.val he⟩

end GlobalTheory.TwLangAb
