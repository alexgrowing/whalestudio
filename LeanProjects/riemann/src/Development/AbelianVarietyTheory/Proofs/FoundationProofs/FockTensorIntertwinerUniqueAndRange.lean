import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockUniq

theorem genSub_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (N : Submodule ℂ V)
    (h1 : S ⊆ N) (h2 : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S := by
  intro x hx
  simp only [genSub, SetLike.mem_coe, Submodule.mem_sInf]
  exact fun N hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V)
    (hy : y ∈ genSub act S) : act Z y ∈ genSub act S := by
  simp only [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  intro p q n T0 T1 T2 F M₁ W M I e₀ v₀ hgen hK hirr hM he hv hI
  refine ⟨?_, ?_, ?_⟩
  · intro io hio h0
    have h1 : ∀ v, io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := by
      let N : Submodule ℂ M.V := LinearMap.eqLocus (io ∘ₗ TensorProduct.mk ℂ W M.V e₀)
        (I ∘ₗ TensorProduct.mk ℂ M₁.V M.V e₀)
      have hN : ∀ v, v ∈ N ↔ io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
      rcases hM.2 N (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hio.2, ← hI.2, hy]) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (hN v₀).2 h0)) hv
      · intro v
        exact (hN v).1 (h ▸ Submodule.mem_top)
    refine TensorProduct.ext' fun e v => ?_
    let N : Submodule ℂ W := LinearMap.eqLocus (io ∘ₗ (TensorProduct.mk ℂ W M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v ∘ₗ W.subtype)
    have hN : ∀ e, e ∈ N ↔ io (e ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
    have hst : KStable M₁.act (N.map W.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      refine ⟨⟨M₁.act Z w, hK Z hZ w w.2⟩, ?_, rfl⟩
      have hw' := (hN w).1 hw
      refine (hN _).2 ?_
      rw [← hio.1 Z hZ w _ v rfl, hw', hI.1]
    have h0' : (e₀ : M₁.V) ∈ N.map W.subtype := ⟨e₀, (hN e₀).2 (h1 v), rfl⟩
    rcases hirr _ (Submodule.map_subtype_le W N) hst with h | h
    · rw [h, Submodule.mem_bot] at h0'
      exact absurd (Subtype.ext h0') he
    · have : (e : M₁.V) ∈ N.map W.subtype := by rw [h]; exact e.2
      obtain ⟨e', he', hee⟩ := this
      have : e' = e := Subtype.ext hee
      subst this
      simpa using (hN e').1 he'
  · intro I' hI' hW
    refine TensorProduct.ext' fun x v => ?_
    let N : Submodule ℂ M₁.V := LinearMap.eqLocus (I' ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
    have hN : ∀ e, e ∈ N ↔ I' (e ⊗ₜ v) = I (e ⊗ₜ v) := fun v => Iff.rfl
    have := genSub_le M₁.act (W : Set M₁.V) N (fun w hw => (hN w).2 (hW ⟨w, hw⟩ v))
      (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hI'.1, ← hI.1, hy])
    rw [hgen] at this
    exact (hN x).1 (this Submodule.mem_top)
  · intro v
    let f : M₁.V →ₗ[ℂ] Pol p q n 0 := I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v
    have hf : ∀ x, f x = I (x ⊗ₜ v) := fun x => rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have := genSub_le M₁.act (W : Set M₁.V)
        ((genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v))).comap f)
        (fun w hw => subset_genSub F.act1 _ ⟨⟨w, hw⟩, rfl⟩)
        (fun Z y hy => by
          rw [Submodule.mem_comap, hf] at hy ⊢
          rw [← hI.1]
          exact genSub_stable _ _ _ _ hy)
      rw [hgen] at this
      exact this (Submodule.mem_top : x ∈ ⊤)
    · have := genSub_le F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) (LinearMap.range f)
        (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
        (by rintro Z _ ⟨x, rfl⟩; exact ⟨M₁.act Z x, by rw [hf, hf, hI.1]⟩)
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩

end GlobalTheory.FockUniq
