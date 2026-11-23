import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_isIrrSub_of_isAlgClosed :
    ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E)
      (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  intro Γ E _ _ _ a σ U h
  classical
  have hinv : ∀ g, ∀ v ∈ U, (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) v ∈ U :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact h.2.1 g v hv
  let r : Representation E Γ U :=
    { toFun := fun g => (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : U), ((r g v : U) : Fin a → E) = ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec v :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule E U) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : U) ∈ (⊥ : Submodule E U) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map U.subtype ≤ U := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : IsInv σ (W.toSubmodule.map U.subtype) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases h.2.2 _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule E U)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  intro φ
  have hφ : φ ∈ Submodule.span E (Set.range r) := by rw [hs]; trivial
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => (hr g w).symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX, hXw⟩ := hx
    obtain ⟨Y, hY, hYw⟩ := hy
    exact ⟨X + Y, Submodule.add_mem _ hX hY, fun w => by rw [Matrix.add_mulVec, hXw, hYw]; simp⟩
  | smul c x _ hx =>
    obtain ⟨X, hX, hXw⟩ := hx
    exact ⟨c • X, Submodule.smul_mem _ c hX, fun w => by rw [Matrix.smul_mulVec, hXw]; simp⟩

end GlobalTheory.SplitField
