import Mathlib

theorem UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top :
    ∀ {K G ι : Type} [inst : Field K] [inst_1 : Fintype ι]
    [DecidableEq ι] (f : G → Matrix ι ι K),
    Submodule.span K (Set.range f) = ⊤ →
      ∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, (f g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro K G ι _ _ _ f hf N hN
  have key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range f) := by rw [hf]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem a hx
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h1 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
    have h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [h2] at h1
