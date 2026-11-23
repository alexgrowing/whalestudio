import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

namespace GlobalTheory.AbsolutelyIrreduciblePullback

open Formalism.MainNotions.N

def pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) : Submodule K (Fin n → K) where
  carrier := {v | f ∘ v ∈ W}
  add_mem' := by
    intro a b ha hb
    have : f ∘ (a + b) = f ∘ a + f ∘ b := by
      funext i; simp
    show f ∘ (a + b) ∈ W
    rw [this]
    exact W.add_mem ha hb
  zero_mem' := by
    have : f ∘ (0 : Fin n → K) = 0 := by
      funext i; simp
    show f ∘ (0 : Fin n → K) ∈ W
    rw [this]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have : f ∘ (c • v) = f c • (f ∘ v) := by
      funext i; simp
    show f ∘ (c • v) ∈ W
    rw [this]
    exact W.smul_mem _ hv

theorem mem_pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) (v : Fin n → K) : v ∈ pullSub f W ↔ f ∘ v ∈ W := by
  exact Iff.rfl

theorem exists_comp_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (hf : Function.Surjective f)
    {n : ℕ} (w : Fin n → L) : ∃ v : Fin n → K, f ∘ v = w := by
  choose v hv using fun i => hf (w i)
  exact ⟨v, funext hv⟩

theorem isInv_pullSub {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (W : Submodule L (Fin n → L)) (hW : IsInv (mapRep f ρ) W) :
    IsInv ρ (pullSub f W) := by
  intro g v hv
  rw [mem_pullSub] at hv ⊢
  have heq : f ∘ ((ρ g : Matrix (Fin n) (Fin n) K).mulVec v) =
      ((mapRep f ρ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec (f ∘ v) := by
    funext i
    exact RingHom.map_mulVec f _ v i
  rw [heq]
  exact hW g (f ∘ v) hv

theorem absIrrSub_top {Γ : Type} [Group Γ] {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  have hsurj : Function.Surjective (algebraMap K (AlgebraicClosure K)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := AlgebraicClosure K)).2
  have hspan : Submodule.span (AlgebraicClosure K)
      ((fun v => (algebraMap K (AlgebraicClosure K)) ∘ v) '' ((⊤ : Submodule K (Fin n → K)) : Set (Fin n → K))) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
    exact Submodule.subset_span ⟨v, Submodule.mem_top, rfl⟩
  unfold AbsIrrSub IsIrrSub
  rw [hspan]
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact top_ne_bot
  · intro W' _ hW'
    rcases h _ (isInv_pullSub (algebraMap K (AlgebraicClosure K)) ρ W' hW') with h0 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := (mem_pullSub _ _ _).mpr hw
      rw [h0, Submodule.mem_bot] at hv
      subst hv
      rw [Submodule.mem_bot]
      funext i
      simp
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := by
        rw [h1]
        trivial
      exact (mem_pullSub _ _ _).mp hv

end GlobalTheory.AbsolutelyIrreduciblePullback
