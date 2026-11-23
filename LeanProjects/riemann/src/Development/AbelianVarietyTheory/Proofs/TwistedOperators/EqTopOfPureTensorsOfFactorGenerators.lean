import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver

open scoped TensorProduct

namespace GlobalTheory.TensHead

open scoped TensorProduct in
private lemma piOp_tprod {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y i (g (y i))) := by
  unfold _root_.GlobalTheory.TensHead.piOp
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

open scoped TensorProduct in
lemma _root_.GlobalTheory.TensHead.piOp_tprod_update {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by
  rw [piOp_tprod]
  simp

open scoped TensorProduct in
private lemma apply_tmul_mem_of_stab_left {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    {g : Module.End ℂ M₀} (hg : g ∈ Op₀) {a : M₀} {t : ⨂[ℂ] i, M i} (h : a ⊗ₜ[ℂ] t ∈ N) :
    g a ⊗ₜ[ℂ] t ∈ N := by
  have hmem : TensorProduct.map g LinearMap.id ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps
    exact Or.inl ⟨g, hg, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  simpa using hN _ hmem _ h

open scoped TensorProduct in
private lemma tmul_tprod_update_apply_mem_of_stab {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    (i : ι) {g : Module.End ℂ (M i)} (hg : g ∈ Op i) {a : M₀} {y : ∀ j, M j} {x : M i}
    (h : a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) :
    a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i (g x)) ∈ N := by
  have hmem : TensorProduct.map LinearMap.id (_root_.GlobalTheory.TensHead.piOp i g) ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps _root_.GlobalTheory.TensHead.piOps
    exact Or.inr ⟨_, ⟨i, g, hg, rfl⟩, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  have := hN _ hmem _ h
  rwa [TensorProduct.map_tmul, LinearMap.id_apply, _root_.GlobalTheory.TensHead.piOp_tprod_update] at this

open scoped TensorProduct in

theorem _root_.GlobalTheory.TensHead.eq_top_of_pure_generators :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → _root_.GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → _root_.GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op₀ Op Rel₀ Rel F₀ F h₀ hF N hRel₀ hRel hN hgen
  have key : ∀ s : Finset ι, ∀ y : ∀ j, M j, (∀ j, j ∉ s → y j ∈ F j) →
      ∀ a : M₀, a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy a
      have hT := h₀ (N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] i, M i)).flip
        (PiTensorProduct.tprod ℂ y))) ?_ ?_ ?_
      · have ha : a ∈ (⊤ : Submodule ℂ M₀) := trivial
        rw [← hT] at ha
        simpa using ha
      · intro x hx
        simpa using hRel₀ x hx _
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hx ⊢
        exact apply_tmul_mem_of_stab_left hN hg hx
      · intro x hx
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
          TensorProduct.mk_apply]
        exact hgen x hx y (fun j => hy j (by simp))
    | insert i s hi ih =>
      intro y hy a
      let S : Submodule ℂ (M i) := ⨅ (b : M₀)
        (z : {z : ∀ j, M j // ∀ j, j ∉ s → j ≠ i → z j ∈ F j}),
        N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) b) ∘ₗ
          (PiTensorProduct.tprod ℂ).toLinearMap z.1 i)
      have hS : ∀ x, x ∈ S ↔ ∀ (b : M₀) (z : ∀ j, M j), (∀ j, j ∉ s → j ≠ i → z j ∈ F j) →
          b ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update z i x) ∈ N := by
        intro x
        simp only [S, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
          MultilinearMap.toLinearMap_apply, TensorProduct.mk_apply, Subtype.forall]
      have hT := hF i S ?_ ?_ ?_
      · have hx : y i ∈ S := by
          rw [hT]
          trivial
        have := (hS _).1 hx a y (fun j hj hji => hy j (by simp [hji, hj]))
        simpa using this
      · intro x hx
        rw [hS]
        intro b z _
        exact hRel i x hx b z
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        rw [hS] at hx ⊢
        intro b z hz
        exact tmul_tprod_update_apply_mem_of_stab hN i hg (hx b z hz)
      · intro x hx
        rw [SetLike.mem_coe, hS]
        intro b z hz
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · rw [Function.update_of_ne hji]
          exact hz j hj hji
  have hall : ∀ v, v ∈ N := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact N.zero_mem
    | tmul a t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r y =>
        rw [TensorProduct.tmul_smul]
        exact N.smul_mem r (key Finset.univ y (fun j hj => absurd (Finset.mem_univ j) hj) a)
      | add p q hp hq =>
        rw [TensorProduct.tmul_add]
        exact N.add_mem hp hq
    | add p q hp hq => exact N.add_mem hp hq
  exact eq_top_iff.2 fun v _ => hall v

end GlobalTheory.TensHead
