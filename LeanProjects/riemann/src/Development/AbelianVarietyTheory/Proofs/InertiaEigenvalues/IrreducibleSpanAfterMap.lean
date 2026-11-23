import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top {k Γ : Type} [Field k] [Group Γ] {L : Type}
    [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : _root_.Formalism.MainNotions.N.Stable (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ)) W) (hne : W ≠ ⊥)
    (hsp : Submodule.span k (Set.range fun g =>
      (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤) :
    _root_.Formalism.MainNotions.N.IsIrrSub (_root_.Formalism.MainNotions.N.mapRep f ρ)
      (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  classical
  have hmul : ∀ (g : Γ) (w : Fin a → k),
      ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) =
        f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w) := by
    intro g w
    funext i
    exact (RingHom.map_mulVec f _ w i).symm
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  let A := Submodule.span L (Set.range T)
  let P : Submodule k (Module.End k W) :=
    { carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)}
      add_mem' := by
        rintro E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
        refine ⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩
        rw [LinearMap.add_apply, h₁, h₂]
        funext i
        simp
      zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩
      smul_mem' := by
        rintro c E ⟨M, hM, h⟩
        refine ⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩
        rw [LinearMap.smul_apply, h]
        funext i
        simp }
  have hP : ∀ E, E ∈ P := by
    have hle : Submodule.span k (Set.range fun g =>
        (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      refine ⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩
      rw [LinearMap.restrict_coe_apply]
      exact hmul g w
    intro E
    apply hle
    rw [hsp]
    exact Submodule.mem_top
  have hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' →
      ∀ M ∈ A, ∀ v ∈ W', M v ∈ W' := by
    intro W' hW' M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hW' g v hv
    | zero => intro v _; simpa using W'.zero_mem
    | add x y _ _ hx hy => intro v hv; exact W'.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; exact W'.smul_mem c (hx v hv)
  unfold _root_.Formalism.MainNotions.N.IsIrrSub
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    apply hw0
    have hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hfw
    funext i
    simpa using congrFun hfw i
  · intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro W' hle hst
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    right
    apply le_antisymm hle
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    rw [Submodule.span_le]
    rintro _ ⟨w₀, hw₀, rfl⟩
    show f ∘ w₀ ∈ W'
    let φ : W →ₗ[k] k := (LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype
    let E : Module.End k W := φ.smulRight ⟨w₀, hw₀⟩
    obtain ⟨M, hMA, hM⟩ := hP E
    have key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))),
        M y = y i • (f ∘ w₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hM ⟨w, hw⟩]
        funext j
        simp [E, φ]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, Pi.add_apply, add_smul]
      | smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]
    have hmem : M x ∈ W' := hA W' hst M hMA x hx
    rw [key x (hle hx)] at hmem
    have hsm := W'.smul_mem (x i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hsm

end GlobalTheory
