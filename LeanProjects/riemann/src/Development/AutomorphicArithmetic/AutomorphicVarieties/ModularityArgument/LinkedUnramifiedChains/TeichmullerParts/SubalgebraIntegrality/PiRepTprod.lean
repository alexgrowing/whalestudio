import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIff
open UpperTheory.V.Z.J.D
open scoped TensorProduct

section Transfer

variable {G G' W W' : Type} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma irr_iff (ρ : Representation ℂ G W) :
    ρ.IsIrreducible ↔ Nontrivial W ∧
      ∀ N : Submodule ℂ W, (∀ g, ∀ v ∈ N, ρ g v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Ra6.irr_iff ρ

private lemma transfer (ρ : Representation ℂ G W) (ρ' : Representation ℂ G' W') (φ : G' → G)
    (hφ : Function.Surjective φ) (e : W' ≃ₗ[ℂ] W)
    (h : ∀ g x, e (ρ' g x) = ρ (φ g) (e x)) (hρ : AbsIrr ρ) : AbsIrr ρ' := by
  obtain ⟨h1, h2⟩ := hρ
  obtain ⟨hW, hN⟩ := (irr_iff ρ).1 h1
  refine ⟨(irr_iff ρ').2 ⟨e.toEquiv.nontrivial, fun N hN' => ?_⟩, fun f hf => ?_⟩
  · have hinv : ∀ g, ∀ v ∈ N.map e.toLinearMap, ρ g v ∈ N.map e.toLinearMap := by
      rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨g', rfl⟩ := hφ g
      exact ⟨ρ' g' x, hN' g' x hx, h g' x⟩
    rcases hN _ hinv with h3 | h3
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := Submodule.mem_map_of_mem hx
      rw [h3, Submodule.mem_bot] at hm
      exact e.map_eq_zero_iff.1 hm
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := by rw [h3]; exact Submodule.mem_top
      obtain ⟨y, hy, hyx⟩ := hm
      rwa [← e.injective hyx]
  · have hs : ∀ g' v, e.symm (ρ (φ g') v) = ρ' g' (e.symm v) := fun g' v => by
      rw [LinearEquiv.symm_apply_eq, h g' (e.symm v), LinearEquiv.apply_symm_apply]
    have hF : Intw ρ ρ (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) := by
      intro g v
      obtain ⟨g', rfl⟩ := hφ g
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hs, hf, h]
    obtain ⟨a, ha⟩ := h2 _ hF
    refine ⟨a, LinearMap.ext fun x => e.injective ?_⟩
    have := LinearMap.congr_fun ha (e x)
    simpa using this

private lemma pt_eq {ι Z : Type} {s : ι → Type} [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    [AddCommGroup Z] [Module ℂ Z] (A B : (⨂[ℂ] i, s i) →ₗ[ℂ] Z)
    (h : ∀ m, A (PiTensorProduct.tprod ℂ m) = B (PiTensorProduct.tprod ℂ m)) (x : ⨂[ℂ] i, s i) :
    A x = B x :=
  LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext h)) x

end Transfer

private lemma piRep_tprod {I : Type} {Gi Wi : I → Type} [∀ i, Group (Gi i)]
    [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) :=
  PiTensorProduct.map_tprod _ _

private def Pp (I : Type) : Prop :=
  ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)), (∀ i, AbsIrr (τ i)) → AbsIrr (piRep τ)

private lemma Pp_equiv {α β : Type} (f : β ≃ α) (h : Pp α) : Pp β := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (piRep fun a => τ (f.symm a)) (piRep τ) (Equiv.piCongrLeft' Gi f)
    (Equiv.surjective _) (PiTensorProduct.reindex ℂ Wi f) (fun g x => ?_)
    (h (fun a => Gi (f.symm a)) (fun a => Wi (f.symm a)) (fun a => τ (f.symm a)) fun a => hτ _)
  refine pt_eq ((PiTensorProduct.reindex ℂ Wi f).toLinearMap ∘ₗ piRep τ g)
    ((piRep (fun a => τ (f.symm a)) (Equiv.piCongrLeft' Gi f g)) ∘ₗ
      (PiTensorProduct.reindex ℂ Wi f).toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod, PiTensorProduct.reindex_tprod]
  rfl

private lemma absIrr_triv : AbsIrr (Representation.trivial ℂ Unit ℂ) := by
  refine ⟨(irr_iff _).2 ⟨inferInstance, fun N _ => eq_bot_or_eq_top N⟩, fun f _ => ⟨f 1, ?_⟩⟩
  refine LinearMap.ext_ring ?_
  simp

private lemma Pp_empty : Pp PEmpty := by
  intro Gi Wi _ _ _ τ _
  refine transfer (Representation.trivial ℂ Unit ℂ) (piRep τ) (fun _ => ()) (fun _ => ⟨1, rfl⟩)
    (PiTensorProduct.isEmptyEquiv PEmpty) (fun g x => ?_) absIrr_triv
  refine pt_eq ((PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap ∘ₗ piRep τ g)
    (Representation.trivial ℂ Unit ℂ () ∘ₗ (PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma Pp_unit : Pp PUnit := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (τ PUnit.unit) (piRep τ) (fun g => g PUnit.unit) (fun h => ⟨fun _ => h, rfl⟩)
    (PiTensorProduct.subsingletonEquiv PUnit.unit) (fun g x => ?_) (hτ _)
  refine pt_eq ((PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap ∘ₗ piRep τ g)
    (τ PUnit.unit (g PUnit.unit) ∘ₗ (PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]

private lemma Pp_sum (hB : BoxIrr) {α β : Type} (ha : Pp α) (hb : Pp β) : Pp (α ⊕ β) := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))) (piRep τ)
    (fun g => (fun a => g (.inl a), fun b => g (.inr b)))
    (fun p => ⟨fun s => Sum.rec (motive := Gi) p.1 p.2 s, rfl⟩)
    (PiTensorProduct.tmulEquivDep ℂ Wi).symm (fun g x => ?_)
    (hB _ _ _ _ _ _ (ha _ _ _ fun a => hτ _) (hb _ _ _ fun b => hτ _))
  refine pt_eq ((PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap ∘ₗ piRep τ g)
    ((box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))
        (fun a => g (.inl a), fun b => g (.inr b))) ∘ₗ
      (PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply]
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, TensorProduct.map_tmul]
  simp [piRep_tprod]

theorem UpperTheory.V.Z.J.D.piIrr :
    BoxIrr → PiIrr := by
  intro hB I _ _ Gi Wi _ _ _ τ hτ
  have key : ∀ (α : Type) [Fintype α], Pp α := by
    refine Fintype.induction_empty_option (P := fun α _ => Pp α) ?_ Pp_empty ?_
    · intro α β _ e h
      exact Pp_equiv e.symm h
    · intro α _ h
      exact Pp_equiv (Equiv.optionEquivSumPUnit α) (Pp_sum hB h Pp_unit)
  exact key I Gi Wi τ hτ
