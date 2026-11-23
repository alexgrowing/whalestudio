import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section Ins

variable {I : Type} [DecidableEq I]

private def ins {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) : ∀ i, β i :=
  fun i => if h : i = i₀ then h ▸ a else b ⟨i, h⟩

private lemma ins_self {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) :
    ins i₀ a b i₀ = a := by
  simp [ins]

private lemma ins_ne {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1)
    (j : {i // i ≠ i₀}) : ins i₀ a b j.1 = b j := by
  simp [ins, j.2]

private lemma ins_res {β : I → Type} (i₀ : I) (g : ∀ i, β i) :
    ins i₀ (g i₀) (fun j => g j.1) = g := by
  funext i
  by_cases h : i = i₀
  · subst h; exact ins_self _ _ _
  · exact ins_ne i₀ _ _ ⟨i, h⟩

private def insHom (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) →* ∀ i, Gi i where
  toFun p := ins i₀ p.1 p.2
  map_one' := by
    funext i
    by_cases h : i = i₀
    · subst h; exact ins_self _ _ _
    · exact ins_ne i₀ _ _ ⟨i, h⟩
  map_mul' p q := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp only [Pi.mul_apply, ins_self, Prod.fst_mul]
    · have := fun (r : Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) => ins_ne i₀ r.1 r.2 ⟨i, h⟩
      simp only [Pi.mul_apply] at this ⊢
      rw [this, this, this]
      rfl

private lemma insHom_res (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (g : ∀ i, Gi i) :
    insHom Gi i₀ (g i₀, fun j => g j.1) = g :=
  ins_res i₀ g

private lemma insHom_inl (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (insHom Gi i₀).comp (MonoidHom.inl _ _) = MonoidHom.mulSingle Gi i₀ := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
    exact ins_ne i₀ _ _ ⟨i, h⟩

private lemma insHom_inr (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (j : {i // i ≠ i₀}) :
    ((insHom Gi i₀).comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : {i // i ≠ i₀} => Gi j.1) j) =
      MonoidHom.mulSingle Gi j.1 := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_of_ne (Ne.symm j.2)]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply]
    refine (ins_ne i₀ _ _ ⟨i, h⟩).trans ?_
    by_cases hj : i = j.1
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      have e : (⟨i, h⟩ : {i // i ≠ i₀}) ≠ j := fun e => hj (congrArg Subtype.val e)
      change (Pi.mulSingle j a : ∀ j : {i // i ≠ i₀}, Gi j.1) ⟨i, h⟩ = 1
      rw [Pi.mulSingle_eq_of_ne e]

private lemma res_update {β : I → Type} (i₀ i : I) (h : i ≠ i₀) (m : ∀ i, β i) (x : β i)
    [DecidableEq {i // i ≠ i₀}] [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i x j.1) =
      Function.update (fun j : {i // i ≠ i₀} => m j.1) ⟨i, h⟩ x := by
  funext j
  by_cases hj : j = ⟨i, h⟩
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Subtype.ext e))]

private lemma res_update_self {β : I → Type} (i₀ : I) (m : ∀ i, β i) (x : β i₀) [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i₀ x j.1) = fun j : {i // i ≠ i₀} => m j.1 :=
  funext fun j : {i // i ≠ i₀} => Function.update_of_ne j.2 _ _

private def split (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    (⨂[ℂ] i, Wi i) →ₗ[ℂ] Wi i₀ ⊗[ℂ] (⨂[ℂ] j : {i // i ≠ i₀}, Wi j.1) :=
  PiTensorProduct.lift
    { toFun := fun m => m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1)
      map_update_add' := by
        intro _ m i x y
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.add_tmul]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_add, TensorProduct.tmul_add]
      map_update_smul' := by
        intro _ m i c x
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.smul_tmul']
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_smul, TensorProduct.tmul_smul] }

private lemma split_tprod (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I)
    (m : ∀ i, Wi i) :
    split Wi i₀ (PiTensorProduct.tprod ℂ m) =
      m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1) := by
  simp [split]

private lemma split_range (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    LinearMap.range (split Wi i₀) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul w t =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      refine ⟨r • PiTensorProduct.tprod ℂ (ins i₀ w m), ?_⟩
      rw [map_smul, split_tprod, ins_self, TensorProduct.tmul_smul]
      congr 3
      funext j
      exact ins_ne i₀ _ _ j
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add, hx, hy, TensorProduct.tmul_add]⟩

private lemma piRep_tprod {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) := by
  simp only [piRep, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

private lemma split_intw [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (i₀ : I) (g : ∀ i, Gi i)
    (t : ⨂[ℂ] i, Wi i) :
    split Wi i₀ (piRep τ g t) =
      box (τ i₀) (piRep fun j : {i // i ≠ i₀} => τ j.1) (g i₀, fun j => g j.1) (split Wi i₀ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul, piRep_tprod, split_tprod, split_tprod]
    simp only [box, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, piRep_tprod]
  | add a b ha hb => simp only [map_add, ha, hb]

end Ins

private lemma piIsot_empty {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I] (Gi Wi : I → Type)
    [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (κ : Representation ℂ (∀ i, Gi i) X) : Isot κ (piRep τ) := by
  intro x _
  let f : (⨂[ℂ] i, Wi i) →ₗ[ℂ] X :=
    (LinearMap.toSpanSingleton ℂ X x).comp (PiTensorProduct.isEmptyEquiv I).toLinearMap
  have hf : Intw (piRep τ) κ f := by
    intro g v
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨PiTensorProduct.tprod ℂ isEmptyElim, ?_⟩
  simp [f, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma piIsot_card (hB : BoxIsot) (hP : PiIrr) (n : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n → ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)]
      [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)),
      (∀ i, AbsIrr (τ i)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      (κ : Representation ℂ (∀ i, Gi i) X), (∀ i, Isot (κ.comp (MonoidHom.mulSingle Gi i)) (τ i)) →
      Isot κ (piRep τ) := by
  induction n with
  | zero =>
    intro I _ _ hc Gi Wi _ _ _ τ _ X _ _ κ _
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.1 hc
    exact piIsot_empty Gi Wi τ κ
  | succ n ih =>
    intro I _ _ hc Gi Wi _ _ _ τ hτ X _ _ κ hκ
    haveI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hJ : Fintype.card {i // i ≠ i₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let J := {i // i ≠ i₀}
    let κ' : Representation ℂ (Gi i₀ × ∀ j : J, Gi j.1) X := κ.comp (insHom Gi i₀)
    have h1 : Isot (κ'.comp (MonoidHom.inl _ _)) (τ i₀) := by
      have : κ'.comp (MonoidHom.inl _ _) = κ.comp (MonoidHom.mulSingle Gi i₀) := by
        rw [← insHom_inl]; rfl
      rw [this]
      exact hκ i₀
    have h2 : Isot (κ'.comp (MonoidHom.inr _ _)) (piRep fun j : J => τ j.1) := by
      refine ih J hJ (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) (fun j => hτ j.1) X
        (κ'.comp (MonoidHom.inr _ _)) fun j => ?_
      have : (κ'.comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : J => Gi j.1) j) =
          κ.comp (MonoidHom.mulSingle Gi j.1) := by
        rw [← insHom_inr]; rfl
      rw [this]
      exact hκ j.1
    have h3 := hB _ _ _ _ (τ i₀) (piRep fun j : J => τ j.1) (hτ i₀)
      (hP J (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) fun j => hτ j.1) X κ' h1 h2
    refine le_trans h3 (iSup_le fun f => ?_)
    have hf : Intw (piRep τ) κ (f.1.comp (split Wi i₀)) := by
      intro g t
      have := f.2 (g i₀, fun j => g j.1) (split Wi i₀ t)
      simp only [LinearMap.comp_apply]
      rw [split_intw, this]
      change κ (insHom Gi i₀ _) _ = _
      rw [insHom_res]
    refine le_iSup_of_le ⟨_, hf⟩ ?_
    rw [LinearMap.range_comp_of_range_eq_top _ (split_range Wi i₀)]

theorem piIsot :
    BoxIsot → PiIrr → PiIsot := by
  intro hB hP I _ _ Gi Wi _ _ _ τ hτ X _ _ κ hκ
  exact piIsot_card hB hP _ I rfl Gi Wi τ hτ X κ hκ

end UpperTheory.V.Z.J.D
