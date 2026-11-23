import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
variable {Q : Type} [Field Q] {G V V' B : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
  [AddCommGroup B] [Module Q B]

private def fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (r g) (a g) - LinearMap.id)

private theorem mem_fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B)
    (x : V ⊗[Q] B) : x ∈ fixT r a ↔ ∀ g, AlgebraTensorModule.map (r g) (a g) x = x := by
  simp [fixT, Submodule.mem_iInf, sub_eq_zero]

private theorem prodLeft_act (r : V →ₗ[Q] V) (r' : V' →ₗ[Q] V') (a : B →ₗ[Q] B) (x : (V × V') ⊗[Q] B) :
    TensorProduct.prodLeft Q Q V V' B (AlgebraTensorModule.map (r.prodMap r') a x) =
      (AlgebraTensorModule.map r a (TensorProduct.prodLeft Q Q V V' B x).1,
        AlgebraTensorModule.map r' a (TensorProduct.prodLeft Q Q V V' B x).2) := by
  induction x with
  | zero => simp [Prod.ext_iff]
  | tmul v b => obtain ⟨v, v'⟩ := v; simp
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

private theorem fixT_map (r : G → V →ₗ[Q] V) (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) :
    (fixT (fun g => (r g).prodMap (r' g)) a).map (TensorProduct.prodLeft Q Q V V' B).toLinearMap =
      (fixT r a).prod (fixT r' a) := by
  ext y
  obtain ⟨x, rfl⟩ := (TensorProduct.prodLeft Q Q V V' B).surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_prod, mem_fixT, mem_fixT, mem_fixT,
    ← forall_and]
  refine forall_congr' fun g => ?_
  rw [← (TensorProduct.prodLeft Q Q V V' B).injective.eq_iff, prodLeft_act, Prod.ext_iff]

private def prodEquiv' {M N : Type} [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module Q N]
    (p : Submodule Q M) (q : Submodule Q N) : ↥(p.prod q) ≃ₗ[Q] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixT_finite [FiniteDimensional Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) : Module.Finite Q ↥(fixT r a) := by
  rcases Nat.eq_zero_or_pos (finrank Q V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos (Nat.pos_of_ne_zero hn) h0)

private theorem fixT_prod [FiniteDimensional Q V] [FiniteDimensional Q V'] (r : G → V →ₗ[Q] V)
    (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) (h' : finrank Q ↥(fixT r' a) = n * finrank Q V') :
    finrank Q ↥(fixT (fun g => (r g).prodMap (r' g)) a) = n * finrank Q (V × V') := by
  haveI := fixT_finite r a hn h
  haveI := fixT_finite r' a hn h'
  rw [← LinearEquiv.finrank_map_eq (TensorProduct.prodLeft Q Q V V' B), fixT_map,
    (prodEquiv' _ _).finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end

theorem UpperTheory.V.Loc.isCrys_isDR_prod :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → (IsCr φ ρ → IsCr φ ρ' → IsCr φ (ρ.prod ρ')) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ (ρ.prod ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _
  have ho : IsOpen (φ.range : Set (GQ l)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ ho
  have h1 : φ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (φ.range ⊔ Iq l).index ≠ 0 := fun h =>
    h1 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_left))
  exact ⟨fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQ (φ g)).toLinearMap) h2 h h',
    fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQdR (φ g)).toLinearMap) h1 h h'⟩
