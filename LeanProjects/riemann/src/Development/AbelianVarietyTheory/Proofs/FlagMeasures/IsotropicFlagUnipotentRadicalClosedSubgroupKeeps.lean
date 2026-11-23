import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.UnipRad

variable {n : ℕ} {ε : Fin n → Bool}

private lemma uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

private lemma uMat_one' : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

private lemma inv_mulVec_mulVec (g : Formalism.REAL.UJ ε) (y : Fin n → ℂ) : uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← uMat_mul', inv_mul_cancel, uMat_one', Matrix.one_mulVec]

lemma inv_keeps (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, uMat g *ᵥ y ∈ V) :
    ∀ y ∈ V, uMat g⁻¹ *ᵥ y ∈ V := by
  intro y hy
  have h' : ∀ y ∈ V, Matrix.toLin' (uMat g) y ∈ V := fun y hy => by simpa using h y hy
  have hinj : Function.Injective ((Matrix.toLin' (uMat g)).restrict h') := by
    intro x z hxz
    have h1 : uMat g *ᵥ (x : Fin n → ℂ) = uMat g *ᵥ (z : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxz
    apply Subtype.ext
    rw [← inv_mulVec_mulVec g x, h1, inv_mulVec_mulVec]
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨y, hy⟩
  have h1 : uMat g *ᵥ (x : Fin n → ℂ) = y := by simpa using congrArg Subtype.val hx
  rw [← h1, inv_mulVec_mulVec]
  exact x.2

lemma keeps {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) (i : Fin (a + 1)) : ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  intro y hy
  induction i using Fin.cases with
  | zero =>
    rw [hW.1] at hy ⊢
    rw [(Submodule.mem_bot ℂ).mp hy]
    simp
  | succ i =>
    have h1 := hW.2.1 (Fin.castSucc_le_succ i) (hu.1 i y hy)
    simpa using (W i.succ).add_mem h1 hy

private lemma step_mul (g h : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) (h2 : uMat h *ᵥ y - y ∈ V) :
    uMat (g * h) *ᵥ y - y ∈ V := by
  have := V.add_mem (hk _ h2) h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← uMat_mul'] at this
  simpa using this

private lemma step_inv (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) :
    uMat g⁻¹ *ᵥ y - y ∈ V := by
  have := V.neg_mem (inv_keeps g V hk _ h1)
  rw [Matrix.mulVec_sub, inv_mulVec_mulVec] at this
  simpa using this

private lemma closed_step (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    IsClosed {g : Formalism.REAL.UJ ε | uMat g *ᵥ y - y ∈ V} := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact V.closed_of_finiteDimensional.preimage
    ((hc.matrix_mulVec continuous_const).sub continuous_const)

theorem flagN_subgroup_closed_keeps (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) :
    (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧
      ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  refine ⟨⟨{ carrier := flagN ε W, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩, ?_,
    fun u hu i => keeps hW u hu i⟩
  · intro g h hg hh
    exact ⟨fun i y hy => step_mul g h _ y (keeps hW g hg _) (hg.1 i y hy) (hh.1 i y hy),
      fun y hy => step_mul g h _ y (keeps hW g hg _) (hg.2 y hy) (hh.2 y hy)⟩
  · refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
    · rw [uMat_one', Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
  · intro g hg
    exact ⟨fun i y hy => step_inv g _ y (keeps hW g hg _) (hg.1 i y hy),
      fun y hy => step_inv g _ y (keeps hW g hg _) (hg.2 y hy)⟩
  · unfold flagN
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y)

end GlobalTheory.FlagMeas.UnipRad
