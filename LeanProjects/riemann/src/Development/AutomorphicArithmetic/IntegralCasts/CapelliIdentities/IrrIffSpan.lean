import Mathlib

private theorem UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ s ∈ S, ∀ v ∈ N, s v ∈ N) → N = ⊥ ∨ N = ⊤) : S = ⊤ := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [eq_top_iff]
    intro f _
    rw [Subsingleton.elim f 0]
    exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun s hs v hv => N.smul_mem (⟨s, hs⟩ : S) hv) with h1 | h1
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).1 h1)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).1 h1)
  rw [eq_top_iff]
  intro f _
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K
          (A := S) (V := V)).2 φ
        exact f.map_smul c v }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) :=
    b.ext fun i => hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem UpperTheory.Reformulated.B.Qe4.irrIffSpan :
    ∀ {K G ι : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : Group G]
    [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (ρ : G →* Matrix ι ι K),
    (∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, ((ρ : G → Matrix ι ι K) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔
      Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) = ⊤ := by
  intro K G ι _ _ _ _ _ ρ
  constructor
  · intro h
    have hmul : ∀ x y : Matrix ι ι K, x ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        x * y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨a * c, map_mul ρ a c⟩
    let A : Subalgebra K (Matrix ι ι K) :=
      (Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K))).toSubalgebra
        (Submodule.subset_span ⟨1, map_one ρ⟩) hmul
    let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
    have hS : A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) = ⊤ := by
      refine UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top _ fun N hN => h N fun g v hv => ?_
      exact hN (e (ρ g)) ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩ v hv
    rw [eq_top_iff]
    intro M _
    have hM : e M ∈ A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) := by
      rw [hS]; exact Algebra.mem_top
    obtain ⟨x, hx, hxe⟩ := hM
    have : x = M := e.injective hxe
    rw [← this]
    exact hx
  · intro h N hN
    have hall : ∀ M : Matrix ι ι K, ∀ v ∈ N, M.mulVec v ∈ N := by
      intro M v hv
      have hM : M ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
        rw [h]; exact Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g v hv
      | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
      | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
      | smul c x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem c hx
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hb
    rw [eq_top_iff]
    intro w _
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    have := hall (LinearMap.toMatrix' (φ.smulRight w)) v hv
    rw [LinearMap.toMatrix'_mulVec] at this
    simpa [hφ] using this
