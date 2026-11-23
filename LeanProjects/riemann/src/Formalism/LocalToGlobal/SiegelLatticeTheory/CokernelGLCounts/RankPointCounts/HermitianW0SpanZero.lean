import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MmIntOfGeneric

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Psi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem MMfam_mem_sup (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
  have hf : ∀ a, t.f a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hf' : ∀ a, t.f' a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  unfold HermSp.MMfam
  rcases M.split with _ | g
  · rcases i with a | a
    · exact hf a
    · exact hf' a
  · rcases i with a | a
    · exact hf a
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' a) (hf a))

theorem hermitian_W0_span_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h w m = 0 := by
  have hle : Submodule.span E (Set.range (H.MMfam t)) ≤ H.Xp t.f ⊔ H.Xp t.f' :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)
  exact hw m (hle hm)

theorem hermitian_span_W0_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h m w = 0 := by
  rw [H.h_herm, hermitian_W0_span_zero H t hw hm, map_zero]

def psiSharp (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    ↥(ThSharp H t₁ N₁) ≃ₗ[M.L.O] ↥(ThSharp H t₂ N₂) where
  toFun x := ⟨ψ ⟨x.1, x.2.1⟩, (ψ ⟨x.1, x.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₂.f t₂.f' := hN₂ hn
    have e : ψ (ψ.symm ⟨n, hnW⟩) = ⟨n, hnW⟩ := ψ.apply_symm_apply _
    have h1 : ((ψ.symm ⟨n, hnW⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁ := by
      rw [hN, e]; exact hn
    have h2 := x.2.2 _ h1
    have h3 := hψ ⟨x.1, x.2.1⟩ (ψ.symm ⟨n, hnW⟩)
    rw [e] at h3
    rw [h3]
    exact h2⟩
  invFun y := ⟨ψ.symm ⟨y.1, y.2.1⟩, (ψ.symm ⟨y.1, y.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₁.f t₁.f' := hN₁ hn
    have h1 : ((ψ ⟨n, hnW⟩ : ↥(H.W0 t₂.f t₂.f')) : V) ∈ N₂ := (hN ⟨n, hnW⟩).1 hn
    have h2 := y.2.2 _ h1
    have h3 := hψ (ψ.symm ⟨y.1, y.2.1⟩) ⟨n, hnW⟩
    rw [ψ.apply_symm_apply] at h3
    rw [← h3]
    exact h2⟩
  map_add' x y := by
    apply Subtype.ext
    have e : (⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        ⟨x.1, x.2.1⟩ + ⟨y.1, y.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) + ((ψ ⟨y.1, y.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    have e : (⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        (c : E) • ⟨x.1, x.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      (c : E) • ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_smul]
    rfl
  left_inv x := by
    apply Subtype.ext
    show ((ψ.symm ⟨(ψ ⟨x.1, x.2.1⟩ : V), _⟩ : ↥(H.W0 t₁.f t₁.f')) : V) = x.1
    rw [Subtype.coe_eta, ψ.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    show ((ψ ⟨(ψ.symm ⟨y.1, y.2.1⟩ : V), _⟩ : ↥(H.W0 t₂.f t₂.f')) : V) = y.1
    rw [Subtype.coe_eta, ψ.apply_symm_apply]

theorem psiSharp_val (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) (x : ↥(ThSharp H t₁ N₁)) :
    ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) = (ψ ⟨x.1, x.2.1⟩ : V) := rfl

def psiTilde (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    DDW H t₁ N₁ ≃ₗ[M.L.O] DDW H t₂ N₂ :=
  Submodule.Quotient.equiv _ _ (psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) ∈ N₂
      rw [psiSharp_val]
      exact (hN _).1 hx
    · intro hy
      refine ⟨(psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      change ((ψ.symm ⟨y.1, y.2.1⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁
      rw [hN (ψ.symm ⟨y.1, y.2.1⟩), ψ.apply_symm_apply]
      exact hy)

theorem psiTilde_mk (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) (x : ↥(ThSharp H t₁ N₁)) :
    psiTilde H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN (dwMk H t₁ N₁ x) =
      dwMk H t₂ N₂ (psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x) := rfl

end Psi

end Formalism.L2.SG.LsDatumA
