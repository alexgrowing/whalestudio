import ReciprocityTheory.GroupCohomology.LocaliseA

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  refine isLocalized_of_cx j.hom t ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

theorem trunc_holds : TruncStatement.{u} := by
  intro R _ A L
  refine ⟨truncCx A L, truncHom A L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_zero] at hc
      rw [cls_eq_zero_iff, mem_B_zero]
      exact Subtype.ext hc
  · intro c
    induction c using H_ind with
    | h x hx =>
      exact ⟨(truncCx A L).cls 0 ⟨x, Submodule.mem_top⟩ (Subtype.ext hx), rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_succ] at hc
      obtain ⟨y, hy⟩ := hc
      rw [cls_eq_zero_iff, mem_B_succ]
      exact ⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩
  · ext c
    constructor
    · rintro ⟨c', rfl⟩
      induction c' using H_ind with
      | h x hx =>
        rw [Hom.H_cls]
        obtain ⟨_, h⟩ := (mem_truncW_one A L).1 x.2
        exact h
    · intro hc
      obtain ⟨x, hx, rfl⟩ := exists_cls c
      have hm : x ∈ truncW A L 1 := (mem_truncW_one A L).2 ⟨hx, hc⟩
      exact ⟨(truncCx A L).cls 1 ⟨x, hm⟩ (Subtype.ext hx), rfl⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    constructor
    intro a b
    induction a using H_ind with
    | h x hx =>
    induction b using H_ind with
    | h y hy =>
      have h1 : x = 0 := Subtype.ext ((Submodule.mem_bot R).1 x.2)
      have h2 : y = 0 := Subtype.ext ((Submodule.mem_bot R).1 y.2)
      subst h1 h2; rfl

end ReciprocityTheory.Coh
