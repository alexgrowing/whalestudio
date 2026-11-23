import Mathlib

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor :
    {F : Type} →
      [inst : Field F] →
        {α : Type} →
          {Γ X : α → Type} →
            [inst_1 : (a : α) → Group (Γ a)] →
              [inst_2 : (a : α) → AddCommGroup (X a)] →
                [inst_3 : (a : α) → _root_.Module F (X a)] →
                  ((a : α) → Representation F (Γ a) (X a)) →
                    Representation F ((a : α) → Γ a) (PiTensorProduct F fun (a : α) ↦ X a) :=
    fun {F : Type} [Field F] {α : Type} {Γ X : α → Type} [(a : α) → Group (Γ a)] [(a : α) → AddCommGroup (X a)]
        [(a : α) → _root_.Module F (X a)] (ρ : (a : α) → Representation F (Γ a) (X a)) ↦
      PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun (a : α) ↦ MonoidHom.comp (ρ a) (Pi.evalMonoidHom Γ a))

noncomputable def UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one :
    {s : ℕ} →
      {G V : Fin s → Type} →
        [inst : (a : Fin s) → Group (G a)] →
          [inst_1 : (a : Fin s) → AddCommGroup (V a)] →
            [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] →
              ((a : Fin s) → Representation ℂ (G a) (V a)) → (a : Fin s) → Representation ℂ (G a) (PiTensorProduct ℂ V) :=
    fun {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)] [(a : Fin s) → AddCommGroup (V a)]
        [(a : Fin s) → _root_.Module ℂ (V a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) ↦
      MonoidHom.comp (UpperTheory.Reformulated.B.SmoothTensorFactor.piTensor σ) (MonoidHom.mulSingle G a)

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : (i : Fin s) → V i) :
    UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) := by
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.map_tprod]
  rfl

private lemma UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds {s : ℕ} {G V : Fin s → Type} [(a : Fin s) → Group (G a)]
    [(a : Fin s) → AddCommGroup (V a)] [(a : Fin s) → _root_.Module ℂ (V a)]
    [(a : Fin s) → TopologicalSpace (G a)]
    (σ : (a : Fin s) → Representation ℂ (G a) (V a))
    (h : ∀ a, UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) (a : Fin s) (v : PiTensorProduct ℂ V) :
    {g : G a | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v} ∈ nhds (1 : G a) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hopen : {g : G a | σ a g (f a) = f a} ∈ nhds (1 : G a) :=
      (h a (f a)).mem_nhds (by simp)
    refine Filter.mem_of_superset hopen ?_
    intro g hg
    have hg' : σ a g (f a) = f a := hg
    have key : (fun i => σ i ((Pi.mulSingle a g : (i : Fin s) → G i) i) (f i)) = f := by
      funext i
      by_cases hi : i = a
      · subst hi
        simpa using hg'
      · simp [Pi.mulSingle_eq_of_ne hi]
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (r • PiTensorProduct.tprod ℂ f) = _
    rw [map_smul, UpperTheory.Reformulated.B.SmoothTensorFactor.position_tprod, key]
  | add x y hx hy =>
    refine Filter.mem_of_superset (Filter.inter_mem hx hy) ?_
    rintro g ⟨h1, h2⟩
    have h1' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g x = x := h1
    have h2' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g y = y := h2
    change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g (x + y) = x + y
    rw [map_add, h1', h2']

theorem UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth :
    ∀ {s : ℕ} {G V : Fin s → Type} [inst : (a : Fin s) → Group (G a)] [inst_1 : (a : Fin s) → AddCommGroup (V a)]
      [inst_2 : (a : Fin s) → _root_.Module ℂ (V a)] [inst_3 : (a : Fin s) → TopologicalSpace (G a)]
      [∀ (a : Fin s), IsTopologicalGroup (G a)] (σ : (a : Fin s) → Representation ℂ (G a) (V a)),
      (∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (σ a)) →
        ∀ (a : Fin s), UpperTheory.Reformulated.B.SmoothTensorFactor.IsSmooth (UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a) := by
  intro s G V _ _ _ _ _ σ h a v
  let H : Subgroup (G a) :=
    { carrier := {g | UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a g v = v}
      mul_mem' := by
        intro x y hx hy
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        have hy' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a y v = v := hy
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy', hx']
      one_mem' := by
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := by
        intro x hx
        have hx' : UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x v = v := hx
        change UpperTheory.Reformulated.B.SmoothTensorFactor.intersection_update_fsHerm_neg_one σ a x⁻¹ v = v
        conv_lhs => rw [← hx']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_of_mem_nhds H (g := 1) (UpperTheory.Reformulated.B.SmoothTensorFactor.stab_mem_nhds σ h a v)
