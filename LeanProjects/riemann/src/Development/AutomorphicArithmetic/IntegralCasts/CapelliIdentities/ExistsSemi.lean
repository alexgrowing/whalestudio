import Mathlib

theorem UpperTheory.Reformulated.B.Ra9.exists_semi :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : Field K] (M : Type) [inst_2 : AddCommGroup M] [inst_3 : _root_.Module A M] [inst_4 : Algebra A K]
    [Module.Free A M] {C W : Type} [inst_6 : Field C] [inst_7 : AddCommGroup W] [inst_8 : _root_.Module C W] (ι : K ≃+* C)
    (sp : M →+ W),
    (∀ (a : A) (m : M), (sp : M → W) (a • m) = (ι : K → C) ((Algebra.algebraMap A K : A → K) a) • (sp : M → W) m) →
      (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun (i : κ) ↦ (sp : M → W) ((b : κ → M) i)) →
        ∃ (Ψ : TensorProduct A K M →+ W),
          (∀ (k : K) (m : M), (Ψ : TensorProduct A K M → W) (k ⊗ₜ[A] m) = (ι : K → C) k • (sp : M → W) m) ∧
            (∀ (k : K) (v : TensorProduct A K M),
                (Ψ : TensorProduct A K M → W) (k • v) = (ι : K → C) k • (Ψ : TensorProduct A K M → W) v) ∧
              Function.Injective (⇑Ψ : TensorProduct A K M → W) ∧
                ∀ (w : W),
                  w ∈ Submodule.span C (Set.range (⇑sp : M → W)) ↔
                    ∃ (v : TensorProduct A K M), (Ψ : TensorProduct A K M → W) v = w := by
  intro A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli
  classical
  let f : K →+ M →+ W :=
    { toFun := fun k =>
        { toFun := fun m => ι k • sp m
          map_zero' := by simp
          map_add' := by intro x y; simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := by intro x y; ext m; simp [add_smul] }
  have hfa : ∀ (k : K) (m : M), f k m = ι k • sp m := fun _ _ => rfl
  have hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m) := by
    intro r k m
    have h := hsp r m
    rw [hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]
  let Ψ : TensorProduct A K M →+ W := TensorProduct.liftAddHom f hf
  have hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m := fun k m => by
    simp only [Ψ, TensorProduct.liftAddHom_tmul, hfa]
  have hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  refine ⟨Ψ, hΨ, hsemi, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Ψ).2 ?_
    intro v hv
    let b := Module.Free.chooseBasis A M
    let bK := Algebra.TensorProduct.basis K b
    have hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i))
        ((bK.repr v).mapRange ι (map_zero ι)) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      conv_lhs => rw [← bK.linearCombination_repr v]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]
    have hl := (linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)
    have hr : bK.repr v = 0 := by
      ext i
      have h := DFunLike.congr_fun hl i
      simpa using h
    simpa using hr
  · intro w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩
      | zero => exact ⟨0, map_zero Ψ⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add Ψ a c⟩
      | smul c x _ hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨v, rfl⟩
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul k m =>
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
