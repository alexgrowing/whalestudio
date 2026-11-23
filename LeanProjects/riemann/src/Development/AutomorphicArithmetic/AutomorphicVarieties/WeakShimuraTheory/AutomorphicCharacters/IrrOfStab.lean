import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem irr_of_stab {k Γ H : Type} [Field k] [Group Γ] [Group H] (r : Γ →* M4 k) (hr : Irr r)
    (ρ : H →* GL (Fin 4) k)
    (h : ∀ g, ∃ (s : H) (t : k), r g = t • (ρ s : Matrix (Fin 4) (Fin 4) k)) : Af.IsIrr ρ := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have key : ∀ M : Matrix (Fin 4) (Fin 4) k, ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M
    have hM : M ∈ Submodule.span k (Set.range r) := by
      have h1 : Submodule.span k (Set.range r) = ⊤ := hr
      rw [h1]; exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨s, t, hs⟩ := h g
      intro v hv
      rw [hs, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW s v hv)
    | zero => intro v _; rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact W.smul_mem _ (hx v hv)
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hi' : v i ≠ 0 := hi
  refine eq_top_iff.2 fun w _ => ?_
  have h2 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
  have h3 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0 : Matrix (Fin 4) (Fin 4) k).mulVec v = w := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_assoc, inv_mul_cancel₀ hi', mul_one]
  rwa [h3] at h2

theorem UpperTheory.V.Ws.auIrr :
    ∀ {k Γ Γ' : Type} [Field k] [Group Γ] [Group Γ'] (r : Γ →* M4 k) (r' : Γ' →* M4 k), Irr r → (∀ g, ∃ g', r' g' = r g) → Af.IsIrr r'.toHomUnits ∧ ∀ χ : Γ' →* kˣ, Af.IsIrr (Af.tw r'.toHomUnits χ) := by
  intro k Γ Γ' _ _ _ r r' hr h
  refine ⟨irr_of_stab r hr _ fun g => ?_, fun χ => irr_of_stab r hr _ fun g => ?_⟩
  · obtain ⟨s, hs⟩ := h g
    exact ⟨s, 1, by rw [one_smul, ← hs]; rfl⟩
  · obtain ⟨s, hs⟩ := h g
    refine ⟨s, ((χ s : k))⁻¹, ?_⟩
    rw [Af.tw_val, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul, ← hs]
    rfl
