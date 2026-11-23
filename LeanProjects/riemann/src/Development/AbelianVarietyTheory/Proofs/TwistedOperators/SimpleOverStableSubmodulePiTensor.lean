import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver

open scoped TensorProduct

namespace GlobalTheory.PiSimple

open GlobalTheory.TensHead

theorem simpleOver_of_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (e : V ≃ₗ[ℂ] W) (G : Set (Module.End ℂ V)) (G' : Set (Module.End ℂ W))
    (K : Submodule ℂ V) (K' : Submodule ℂ W) (hK : K.map (e : V →ₗ[ℂ] W) = K')
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ x, g' (e x) = e (g x)) (h : SimpleOver G' K') :
    SimpleOver G K := by
  intro N hN hKN
  have hs : Stab G' (N.map (e : V →ₗ[ℂ] W)) := by
    rintro g' hg' _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hc⟩ := hG g' hg'
    exact ⟨g x, hN g hg x hx, by simpa using (hc x).symm⟩
  have hle : K' ≤ N.map (e : V →ₗ[ℂ] W) := hK ▸ Submodule.map_mono hKN
  have key : ∀ P : Submodule ℂ V, (P.map (e : V →ₗ[ℂ] W)).comap (e : V →ₗ[ℂ] W) = P := by
    intro P; ext x; simp
  rcases h _ hs hle with h1 | h1
  · left
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [← hK, key, key] at this
  · right
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [key, Submodule.comap_top] at this

def PP (σ : Type) : Prop :=
  ∀ [DecidableEq σ] (M : σ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Stab (Op i) (K i)) →
    (∀ i, SimpleOver (Op i) (K i)) → SimpleOver (piOps Op) (piKer K)

theorem pp_empty : PP PEmpty := by
  intro _ M _ _ Op K _ _ _
  refine simpleOver_of_equiv (PiTensorProduct.isEmptyEquiv PEmpty) _ (∅ : Set (Module.End ℂ ℂ))
    _ ⊥ ?_ (by simp) ?_
  · have : piKer K = ⊥ := by
      rw [piKer, Submodule.span_eq_bot]
      rintro _ ⟨y, ⟨i, _⟩, _⟩
      exact i.elim
    rw [this, Submodule.map_bot]
  · intro N _ _
    rcases Ideal.eq_bot_or_top (N : Ideal ℂ) with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem pp_unit : PP PUnit := by
  intro _ M _ _ Op K _ _ hso
  let e := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := M) PUnit.unit
  refine simpleOver_of_equiv e _ (Op PUnit.unit) _ (K PUnit.unit) ?_ ?_ (hso _)
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      cases i
      simpa [e] using hi
    · intro x hx
      refine ⟨e.symm x, Submodule.subset_span ⟨_, ⟨PUnit.unit, by simpa using hx⟩, rfl⟩, by simp⟩
  · intro g hg
    refine ⟨piOp PUnit.unit g, ⟨PUnit.unit, g, hg, rfl⟩, fun x => ?_⟩
    have H : g ∘ₗ (e : _ →ₗ[ℂ] M PUnit.unit) = (e : _ →ₗ[ℂ] M PUnit.unit) ∘ₗ piOp PUnit.unit g := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp [e, piOp, PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun H x

theorem pp_of_equiv {σ ι : Type} (f : σ ≃ ι) (hσ : PP σ) : PP ι := by
  intro _ M _ _ Op K hr hs hso
  classical
  have H := hσ (fun s => M (f s)) (fun s => Op (f s)) (fun s => K (f s)) (fun s => hr _)
    (fun s => hs _) (fun s => hso _)
  refine simpleOver_of_equiv (PiTensorProduct.reindex ℂ M f.symm) _ _ _ _ ?_ ?_ H
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ := f.surjective i
      exact Submodule.subset_span ⟨fun s => y (f s), ⟨s, hi⟩, by simp⟩
    · rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨s, hz⟩, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (Equiv.piCongrLeft M f z),
        Submodule.subset_span ⟨_, ⟨f s, by simpa using hz⟩, rfl⟩, ?_⟩
      simp
  · rintro _ ⟨s, g, hg, rfl⟩
    refine ⟨piOp (f s) g, ⟨f s, g, hg, rfl⟩, fun x => ?_⟩
    have hu : (Function.update (fun j => (LinearMap.id : M (f j) →ₗ[ℂ] M (f j))) s g) =
        fun j => Function.update (fun i => (LinearMap.id : M i →ₗ[ℂ] M i)) (f s) g (f.symm.symm j) := by
      funext j
      by_cases h : j = s
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact (Function.update_of_ne (β := fun i => M i →ₗ[ℂ] M i) (a := f j) (a' := f s)
          (fun h' => h (f.injective h')) g (fun i => LinearMap.id)).symm
    simp only [piOp, LinearEquiv.coe_coe]
    rw [hu, PiTensorProduct.map_reindex]

theorem simpleOver_sum {α β : Type} (hα : PP α) (hβ : PP β) [DecidableEq (α ⊕ β)]
    (N : α ⊕ β → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (Op : ∀ i, Set (Module.End ℂ (N i))) (K : ∀ i, Submodule ℂ (N i))
    (hr : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0)
    (hrl : Module.rank ℂ (⨂[ℂ] a, N (.inl a)) ≤ Cardinal.aleph0)
    (hs : ∀ i, Stab (Op i) (K i)) (hso : ∀ i, SimpleOver (Op i) (K i)) :
    SimpleOver (piOps Op) (piKer K) := by
  classical
  have hA := hα (fun a => N (.inl a)) (fun a => Op (.inl a)) (fun a => K (.inl a))
    (fun a => hr _) (fun a => hs _) (fun a => hso _)
  have hB := hβ (fun b => N (.inr b)) (fun b => Op (.inr b)) (fun b => K (.inr b))
    (fun b => hr _) (fun b => hs _) (fun b => hso _)
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan (piOps (fun a => Op (.inl a))) (piOps (fun b => Op (.inr b)))
    (piKer (fun a => K (.inl a))) (piKer (fun b => K (.inr b))) hrl
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun a => hs _)) (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun b => hs _)) hA hB
  let e := (PiTensorProduct.tmulEquivDep ℂ N).symm
  refine simpleOver_of_equiv e _ _ _ _ ?_ ?_ hT
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨PiTensorProduct.tprod ℂ (fun a => y (.inl a)),
        PiTensorProduct.tprod ℂ (fun b => y (.inr b)), ?_, by simp [e]⟩
      cases i with
      | inl a => exact Or.inl (Submodule.subset_span ⟨_, ⟨a, hi⟩, rfl⟩)
      | inr b => exact Or.inr (Submodule.subset_span ⟨_, ⟨b, hi⟩, rfl⟩)
    · set Q := (piKer K).map e.toLinearMap with hQ
      have pure : ∀ (y₁ : ∀ a, N (.inl a)) (y₂ : ∀ b, N (.inr b)),
          ((∃ a, y₁ a ∈ K (.inl a)) ∨ (∃ b, y₂ b ∈ K (.inr b))) →
          PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₁ y₂ h
        refine ⟨PiTensorProduct.tprod ℂ (fun i => Sum.rec y₁ y₂ i),
          Submodule.subset_span ⟨_, ?_, rfl⟩, by simp [e]⟩
        rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
        · exact ⟨.inl a, ha⟩
        · exact ⟨.inr b, hb⟩
      have left : ∀ (y₁ : ∀ a, N (.inl a)), (∃ a, y₁ a ∈ K (.inl a)) →
          ∀ z, PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] z ∈ Q := by
        intro y₁ h z
        have : (⊤ : Submodule ℂ (⨂[ℂ] b, N (.inr b))) ≤
            Q.comap (TensorProduct.mk ℂ _ _ (PiTensorProduct.tprod ℂ y₁)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₂, rfl⟩
          exact pure y₁ y₂ (Or.inl h)
        exact this Submodule.mem_top
      have right : ∀ (y₂ : ∀ b, N (.inr b)), (∃ b, y₂ b ∈ K (.inr b)) →
          ∀ x, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₂ h x
        have : (⊤ : Submodule ℂ (⨂[ℂ] a, N (.inl a))) ≤
            Q.comap ((TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ y₂)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₁, rfl⟩
          exact pure y₁ y₂ (Or.inr h)
        exact this Submodule.mem_top
      rw [tensKer, Submodule.span_le]
      rintro _ ⟨x, z, hxz, rfl⟩
      rcases hxz with hx | hz
      · have : piKer (fun a => K (.inl a)) ≤ Q.comap ((TensorProduct.mk ℂ _ _).flip z) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₁, h, rfl⟩
          exact left y₁ h z
        exact this hx
      · have : piKer (fun b => K (.inr b)) ≤ Q.comap (TensorProduct.mk ℂ _ _ x) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₂, h, rfl⟩
          exact right y₂ h x
        exact this hz
  · rintro _ (⟨_, ⟨a, g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨b, g, hg, rfl⟩, rfl⟩)
    · refine ⟨piOp (Sum.inl a) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map (piOp a g) LinearMap.id) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inl a) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          by_cases h : a' = a
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inl_injective h'))]
        · funext b'
          rw [Function.update_of_ne (Sum.inr_ne_inl)]
          rfl
      exact LinearMap.congr_fun H x
    · refine ⟨piOp (Sum.inr b) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map LinearMap.id (piOp b g)) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inr b) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          rw [Function.update_of_ne (Sum.inl_ne_inr)]
          rfl
        · funext b'
          by_cases h : b' = b
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inr_injective h'))]
      exact LinearMap.congr_fun H x

theorem pp_unit_sum {α : Type} (hα : PP α) : PP (PUnit ⊕ α) := by
  intro _ N _ _ Op K hr hs hso
  refine simpleOver_sum pp_unit hα N Op K hr ?_ hs hso
  rw [(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun u : PUnit => N (Sum.inl u))
    PUnit.unit).rank_eq]
  exact hr _

theorem pp_option {α : Type} (hα : PP α) : PP (Option α) :=
  pp_of_equiv ((Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _)).symm (pp_unit_sum hα)

theorem pp_finite (σ : Type) [Finite σ] : PP σ :=
  Finite.induction_empty_option (P := PP) (fun f h => pp_of_equiv f h) pp_empty
    (fun h => pp_option h) σ

theorem simpleOver_piKer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i)))
    (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  intro ι _ _ M _ _ Op K hr hs hso
  exact pp_finite ι M Op K hr hs hso

end GlobalTheory.PiSimple
