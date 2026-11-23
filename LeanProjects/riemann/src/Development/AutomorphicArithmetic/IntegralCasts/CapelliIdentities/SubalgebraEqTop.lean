import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qe26.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qe26.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qe26.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qe26.IsIrrSub r ⊤

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe26.tr :
    {k : Type} → [inst : Field k] → {n : ℕ} → GL (Fin n) k → k :=
    fun {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) ↦ (↑g : Matrix (Fin n) (Fin n) k).trace

private theorem UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top {k V : Type} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (S : Subalgebra k (Module.End k V))
    (h : ∀ W : Submodule k V, (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    S = ⊤ := by
  have hsimple : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    refine ⟨fun p ↦ ?_⟩
    rcases h (p.restrictScalars k) (fun s hs v hv ↦ p.smul_mem ⟨s, hs⟩ hv) with h1 | h1
    · left
      simpa using h1
    · right
      simpa using h1
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) k
  have hfin : Module.Finite (Module.End S V) V :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  intro T _
  let T' : Module.End (Module.End S V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := hb.2 c
        simp }
  obtain ⟨s, hs⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V) T'
  have : T = s.1 := by
    ext v
    exact (LinearMap.congr_fun hs v).symm
  rw [this]
  exact s.2

private theorem UpperTheory.Reformulated.B.Qe26.lift_surjective {k : Type} [Field k] [IsAlgClosed k] {H : Type}
    [Group H] {n : ℕ} (R : H →* GL (Fin n) k) (hR : UpperTheory.Reformulated.B.Qe26.IsIrr R) :
    Function.Surjective (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R)) := by
  obtain ⟨h0, -, h1⟩ := hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  have hnt : Nontrivial (Fin n → k) := (Submodule.nontrivial_iff k).1 ⟨⟨_, _, h0⟩⟩
  have htop := UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top
    (((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range) (by
      intro W hW
      refine h1 W le_top (fun g v hv ↦ ?_)
      have := hW _ ⟨MonoidAlgebra.single g 1, rfl⟩ v hv
      simpa [hL] using this)
  intro M
  have hM : Matrix.toLinAlgEquiv' M ∈
      ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range := by
    rw [htop]; trivial
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective hx⟩

theorem UpperTheory.Reformulated.B.Qe26.kerLe :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (H : Type) [inst_2 : Group H] (n : ℕ) (R : H →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qe26.IsIrr R →
        ∀ (x₀ : GL (Fin n) k) (B : Type) [inst_3 : Ring B] [inst_4 : Algebra k B] [Module.Finite k B] (φ : H →* B)
          (f : B →ₗ[k] k),
          (∀ (h : H), UpperTheory.Reformulated.B.Qe26.tr (x₀ * (R : H → GL (Fin n) k) h) = (f : B → k) ((φ : H → B) h)) →
            n ^ (2 : ℕ) ≤ Module.finrank k ↥(Algebra.adjoin k (Set.range (⇑φ : H → B))) ∧
              ∀ (x : MonoidAlgebra k H),
                ((MonoidAlgebra.lift k B H : (H →* B) → MonoidAlgebra k H →ₐ[k] B) φ : MonoidAlgebra k H → B) x = (0 : B) →
                  ((MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H :
                            (H →* Matrix (Fin n) (Fin n) k) → MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k)
                          ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) :
                        MonoidAlgebra k H → Matrix (Fin n) (Fin n) k)
                      x =
                    (0 : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ H _ n R hR x₀ B _ _ _ φ f hf
  have hsurj := UpperTheory.Reformulated.B.Qe26.lift_surjective R hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  set Φ := MonoidAlgebra.lift k B H φ with hΦ
  have htr : ∀ y, ((x₀ : Matrix (Fin n) (Fin n) k) * L y).trace = f (Φ y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb]
    | single g c =>
      have := hf g
      simp only [UpperTheory.Reformulated.B.Qe26.tr, Units.val_mul] at this
      simp [hL, hΦ, ← this]
  have hker : ∀ x, Φ x = 0 → L x = 0 := by
    intro x hx
    rw [Matrix.ext_iff_trace_mul_left]
    intro M
    obtain ⟨y, hy⟩ := hsurj ((↑x₀⁻¹ : Matrix (Fin n) (Fin n) k) * M)
    have := htr (y * x)
    rw [map_mul, map_mul, hx, hy, mul_zero, map_zero, ← mul_assoc, Units.mul_inv_cancel_left] at this
    simpa using this
  refine ⟨?_, hker⟩
  have hle : LinearMap.ker Φ.toLinearMap ≤ LinearMap.ker L.toLinearMap := fun x hx ↦ hker x hx
  have hrange : LinearMap.range Φ.toLinearMap ≤
      Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ)) := by
    rintro _ ⟨y, rfl⟩
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | single g c =>
      have : Φ.toLinearMap (MonoidAlgebra.single g c) = c • φ g := by simp [hΦ]
      rw [this]
      exact Submodule.smul_mem _ _ (Algebra.subset_adjoin ⟨g, rfl⟩)
  let ψ : LinearMap.range Φ.toLinearMap →ₗ[k] Matrix (Fin n) (Fin n) k :=
    ((LinearMap.ker Φ.toLinearMap).liftQ L.toLinearMap hle).comp
      Φ.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨y, rfl⟩ := hsurj M
    exact ⟨Φ.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk y), by simp [ψ]⟩
  calc n ^ 2 = Module.finrank k (Matrix (Fin n) (Fin n) k) := by
        simp [Module.finrank_matrix, sq]
    _ ≤ Module.finrank k (LinearMap.range Φ.toLinearMap) :=
        LinearMap.finrank_le_finrank_of_surjective hψ
    _ ≤ Module.finrank k (Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ))) :=
        Submodule.finrank_mono hrange
    _ = _ := rfl
