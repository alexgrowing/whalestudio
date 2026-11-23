import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem cardinal_sum_fintype {I : Type} [Fintype I] (f : I → Cardinal.{0}) :
    Cardinal.sum f = ∑ t, f t := by
  have gen : ∀ (J : Type) [Fintype J] (β : J → Type), Cardinal.mk (Σ j, β j) = ∑ j, Cardinal.mk (β j) := by
    intro J _
    refine Fintype.induction_empty_option
      (P := fun J _ => ∀ β : J → Type, Cardinal.mk (Σ j, β j) = ∑ j, Cardinal.mk (β j)) ?_ ?_ ?_ J
    · intro α γ _ e h β
      rw [← Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := β) e), h (fun a => β (e a))]
      exact @Equiv.sum_comp α γ Cardinal.{0} (Fintype.ofEquiv γ e.symm) _ _ e (fun b => Cardinal.mk (β b))
    · intro β
      simp
    · intro α _ h β
      let e : (Σ j : Option α, β j) ≃ (β none ⊕ Σ a : α, β (some a)) :=
        { toFun := fun p => match p with
            | ⟨none, b⟩ => Sum.inl b
            | ⟨some a, b⟩ => Sum.inr ⟨a, b⟩
          invFun := fun q => match q with
            | Sum.inl b => ⟨none, b⟩
            | Sum.inr ⟨a, b⟩ => ⟨some a, b⟩
          left_inv := by rintro ⟨_ | a, b⟩ <;> rfl
          right_inv := by rintro (b | ⟨a, b⟩) <;> rfl }
      rw [Cardinal.mk_congr e, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
        h (fun a => β (some a)), Fintype.sum_option]
  have hf : f = fun t => Cardinal.mk (Quotient.out (f t)) := by
    funext t
    exact (Cardinal.mk_out (f t)).symm
  rw [hf, ← Cardinal.mk_sigma]
  exact gen I _

private theorem character_orthogonality_distinct {Q I : Type} [Group Q] [Fintype Q] (χ : I → Q →* ℂˣ)
    (hχ : Function.Injective χ) (s t : I) (hst : s ≠ t) :
    ∑ x, (((χ s x)⁻¹ : ℂˣ) : ℂ) * ((χ t x : ℂˣ) : ℂ) = 0 := by
  have hne : χ s ≠ χ t := fun h => hst (hχ h)
  obtain ⟨y, hy⟩ : ∃ y, χ s y ≠ χ t y := by
    by_contra h
    push_neg at h
    exact hne (MonoidHom.ext h)
  have hshift : ∑ x, (((χ s x)⁻¹ : ℂˣ) : ℂ) * ((χ t x : ℂˣ) : ℂ) =
      ((((χ s y)⁻¹ * χ t y : ℂˣ)) : ℂ) * ∑ x, (((χ s x)⁻¹ : ℂˣ) : ℂ) * ((χ t x : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft y)
      (fun x => (((χ s (y * x))⁻¹ : ℂˣ) : ℂ) * ((χ t (y * x) : ℂˣ) : ℂ)) _ (fun x => rfl)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have hg : ((((χ s y)⁻¹ * χ t y : ℂˣ)) : ℂ) ≠ 1 := by
    rw [Ne, Units.val_eq_one, inv_mul_eq_one]
    exact hy
  have h0 : (((((χ s y)⁻¹ * χ t y : ℂˣ)) : ℂ) - 1) *
      ∑ x, (((χ s x)⁻¹ : ℂˣ) : ℂ) * ((χ t x : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, ← hshift]
    ring
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (sub_eq_zero.1 h) hg
  · exact h

private theorem rank_isotypic_character_projection {Q I W : Type} [Group Q] [Fintype Q] [Fintype I] [AddCommGroup W]
    [Module ℂ W] (V : Submodule ℂ W) (T : Q → Module.End ℂ W)
    (hV : ∀ x, ∀ v ∈ V, T x v ∈ V) (hmul : ∀ x y, ∀ v ∈ V, T x (T y v) = T (x * y) v)
    (χ : I → Q →* ℂˣ) (hχ : Function.Injective χ) (c : Q → ℤ)
    (hc : ∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) :
    Module.rank ℂ ↥(V ⊓ LinearMap.ker ((∑ x, c x • T x) - ((Fintype.card Q : ℕ) : Module.End ℂ W))) =
      ∑ t, Module.rank ℂ ↥(V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ t x : ℂˣ) : ℂ)) := by
  classical
  have hn : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨e, he_apply⟩ : ∃ e : I → Module.End ℂ W, ∀ t v,
      e t v = (Fintype.card Q : ℂ)⁻¹ • ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) • T x v :=
    ⟨fun t => (Fintype.card Q : ℂ)⁻¹ • ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) • T x, fun t v => by simp⟩
  have heV : ∀ t, ∀ v ∈ V, e t v ∈ V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ t x : ℂˣ) : ℂ) := by
    intro t v hv
    refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun y => ?_⟩
    · rw [he_apply]
      exact Submodule.smul_mem V _ (Submodule.sum_mem V fun x _ => Submodule.smul_mem V _ (hV x v hv))
    · rw [Module.End.mem_eigenspace_iff, he_apply, map_smul, map_sum]
      have h1 : ∀ x, T y ((((χ t x)⁻¹ : ℂˣ) : ℂ) • T x v) = (((χ t x)⁻¹ : ℂˣ) : ℂ) • T (y * x) v := by
        intro x
        rw [map_smul, hmul y x v hv]
      simp only [h1]
      rw [smul_comm ((χ t y : ℂˣ) : ℂ) ((Fintype.card Q : ℂ)⁻¹)]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft y) (fun x => (((χ t x)⁻¹ : ℂˣ) : ℂ) • T (y * x) v)
        (fun z => ((χ t y : ℂˣ) : ℂ) • ((((χ t z)⁻¹ : ℂˣ) : ℂ) • T z v)) ?_
      intro x
      simp only [Equiv.coe_mulLeft]
      rw [smul_smul]
      congr 1
      have h2 := (χ t y).ne_zero
      have h3 := (χ t x).ne_zero
      simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
  have hproj : ∀ s t, ∀ w ∈ V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ s x : ℂˣ) : ℂ),
      e t w = if s = t then w else 0 := by
    intro s t w hw
    have hT : ∀ x, T x w = ((χ s x : ℂˣ) : ℂ) • w := fun x =>
      Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hw).2 x)
    rw [he_apply]
    simp only [hT, smul_smul]
    rw [← Finset.sum_smul, smul_smul]
    split_ifs with h
    · subst h
      have h1 : ∀ x, (((χ s x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ) = 1 := fun x => by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [inv_mul_cancel₀ hn, one_smul]
    · rw [character_orthogonality_distinct χ hχ t s (Ne.symm h), mul_zero, zero_smul]
  have hP : ∀ v, (∑ x, c x • T x) v = (Fintype.card Q : ℂ) • ∑ t, e t v := by
    intro v
    have hR : (Fintype.card Q : ℂ) • ∑ t, e t v = ∑ t, ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) • T x v := by
      simp only [he_apply, ← Finset.smul_sum]
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [hR, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℂ (c x) (T x v), hc x, Finset.sum_smul]
  have hker : ∀ v ∈ V, v ∈ LinearMap.ker ((∑ x, c x • T x) - ((Fintype.card Q : ℕ) : Module.End ℂ W)) ↔
      ∑ t, e t v = v := by
    intro v _
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.natCast_apply, sub_eq_zero, hP,
      ← Nat.cast_smul_eq_nsmul ℂ]
    exact (smul_right_injective W hn).eq_iff
  have hsum : ∀ (w : ∀ t, ↥(V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ t x : ℂˣ) : ℂ))) t,
      e t (∑ s, (w s : W)) = w t := by
    intro w t
    rw [map_sum, Finset.sum_eq_single t]
    · rw [hproj t t _ (w t).2, if_pos rfl]
    · intro s _ hst
      rw [hproj s t _ (w s).2, if_neg hst]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsumV : ∀ (w : ∀ t, ↥(V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ t x : ℂˣ) : ℂ))),
      ∑ s, (w s : W) ∈ V := fun w =>
    Submodule.sum_mem V fun s _ => (Submodule.mem_inf.1 (w s).2).1
  let L : ↥(V ⊓ LinearMap.ker ((∑ x, c x • T x) - ((Fintype.card Q : ℕ) : Module.End ℂ W))) ≃ₗ[ℂ]
      (∀ t, ↥(V ⊓ ⨅ x, Module.End.eigenspace (T x) ((χ t x : ℂˣ) : ℂ))) :=
    { toFun := fun v t => ⟨e t v, heV t v (Submodule.mem_inf.1 v.2).1⟩
      map_add' := fun v w => by
        funext t
        apply Subtype.ext
        simp [map_add]
      map_smul' := fun a v => by
        funext t
        apply Subtype.ext
        simp [map_smul]
      invFun := fun w => ⟨∑ s, (w s : W), Submodule.mem_inf.2 ⟨hsumV w,
        (hker _ (hsumV w)).2 (Finset.sum_congr rfl fun t _ => hsum w t)⟩⟩
      left_inv := fun v => Subtype.ext ((hker v (Submodule.mem_inf.1 v.2).1).1 (Submodule.mem_inf.1 v.2).2)
      right_inv := fun w => by
        funext t
        exact Subtype.ext (hsum w t) }
  rw [L.rank_eq, rank_pi, cardinal_sum_fintype]

theorem UpperTheory.rank_fixed_inf_character_eigenspace :
    ∀ {G Q A I : Type} [Group G] [Group Q] [Fintype Q] [Group A] [Fintype I]
        (K : Subgroup G) (ι : A →* G) (π : A →* Q) (s : Q → A), (∀ x, π (s x) = x) →
        (∀ a, π a = 1 ↔ ι a ∈ K) → (∀ a, ∀ u ∈ K, (ι a)⁻¹ * u * ι a ∈ K) →
        ∀ (χ : I → Q →* ℂˣ), Function.Injective χ → ∀ (c : Q → ℤ),
        (∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
        Module.rank ℂ ↥(fixd τ K ⊓ ePart τ (∑ x, Finsupp.single (ι (s x)) (c x)) (Fintype.card Q)) =
          ∑ t, Module.rank ℂ ↥(fixd τ K ⊓ ⨅ y : A, Module.End.eigenspace (τ (ι y)) ((χ t (π y) : ℂˣ) : ℂ)) := by
  intro G Q A I _ _ _ _ _ K ι π s hs hπ hK χ hχ c hc W _ _ τ
  have hfix : ∀ a, π a = 1 → ∀ v ∈ fixd τ K, τ (ι a) v = v := by
    intro a ha v hv
    have hv' : ∀ u ∈ K, τ u v = v := hv
    exact hv' _ ((hπ a).1 ha)
  have hV : ∀ x, ∀ v ∈ fixd τ K, τ (ι (s x)) v ∈ fixd τ K := by
    intro x v hv
    have hv' : ∀ u ∈ K, τ u v = v := hv
    show ∀ u ∈ K, τ u (τ (ι (s x)) v) = τ (ι (s x)) v
    intro u hu
    have h1 := hv' _ (hK (s x) u hu)
    have e : ι (s x) * ((ι (s x))⁻¹ * u * ι (s x)) = u * ι (s x) := by group
    calc τ u (τ (ι (s x)) v) = τ (u * ι (s x)) v := by rw [map_mul]; rfl
      _ = τ (ι (s x) * ((ι (s x))⁻¹ * u * ι (s x))) v := by rw [e]
      _ = τ (ι (s x)) (τ ((ι (s x))⁻¹ * u * ι (s x)) v) := by rw [map_mul]; rfl
      _ = τ (ι (s x)) v := by rw [h1]
  have hmul : ∀ x y, ∀ v ∈ fixd τ K, τ (ι (s x)) (τ (ι (s y)) v) = τ (ι (s (x * y))) v := by
    intro x y v hv
    obtain ⟨a, ha, he⟩ : ∃ a, π a = 1 ∧ s (x * y) = s x * s y * a :=
      ⟨(s x * s y)⁻¹ * s (x * y), by simp [hs], (mul_inv_cancel_left _ _).symm⟩
    rw [he, map_mul ι (s x * s y) a, map_mul τ, Module.End.mul_apply, hfix a ha v hv,
      map_mul ι, map_mul τ, Module.End.mul_apply]
  have hE : opE τ (∑ x, Finsupp.single (ι (s x)) (c x)) = ∑ x, c x • τ (ι (s x)) := by
    unfold opE
    rw [← Finsupp.sum_finset_sum_index (h := fun g (n : ℤ) => n • τ g)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    simp [Finsupp.sum_single_index]
  have hR : ∀ t, fixd τ K ⊓ ⨅ y : A, Module.End.eigenspace (τ (ι y)) ((χ t (π y) : ℂˣ) : ℂ) =
      fixd τ K ⊓ ⨅ x, Module.End.eigenspace (τ (ι (s x))) ((χ t x : ℂˣ) : ℂ) := by
    intro t
    ext v
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    constructor
    · rintro ⟨hv, h⟩
      exact ⟨hv, fun x => by simpa [hs] using h (s x)⟩
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun y => ?_⟩
      obtain ⟨a, ha, hy⟩ : ∃ a, π a = 1 ∧ y = s (π y) * a :=
        ⟨(s (π y))⁻¹ * y, by simp [hs], (mul_inv_cancel_left _ _).symm⟩
      have h2 : τ (ι y) v = τ (ι (s (π y))) v := by
        conv_lhs => rw [hy]
        rw [map_mul ι, map_mul τ, Module.End.mul_apply, hfix a ha v hv]
      rw [h2]
      exact h (π y)
  have key := rank_isotypic_character_projection (fixd τ K) (fun x => τ (ι (s x))) hV hmul χ hχ c hc
  unfold ePart
  rw [hE]
  refine key.trans (Finset.sum_congr rfl fun t _ => ?_)
  rw [hR t]
