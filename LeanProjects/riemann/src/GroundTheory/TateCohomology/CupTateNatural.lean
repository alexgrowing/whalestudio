import Mathlib
import GroundTheory.TateCohomology.CupTate
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Naturality

omit [Fintype G] in

theorem augTensorRight_comm₁₂ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augIdeal k G ◁ φ) ⊗ₘ ψ) ≫ ((augIdealι k G ▷ A') ▷ B') =
      ((augIdealι k G ▷ A) ▷ B) ≫ ((Rep.leftRegular k G ◁ φ) ⊗ₘ ψ) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul t b =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.zero_tmul]
    | tmul i a => rfl
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

omit [Fintype G] in

theorem augTensorRight_comm₂₃ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((Rep.leftRegular k G ◁ φ) ⊗ₘ ψ) ≫ (augX A' ▷ B') = (augX A ▷ B) ≫ (φ ⊗ₘ ψ) := by
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    augX_naturality, Category.comp_id, Category.id_comp]

omit [Fintype G] in

theorem augTensorLeft_comm₁₂ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    (φ ⊗ₘ (augIdeal k G ◁ ψ)) ≫ (A' ◁ (augIdealι k G ▷ B')) =
      (A ◁ (augIdealι k G ▷ B)) ≫ (φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.tmul_zero]
    | tmul i b => rfl
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

omit [Fintype G] in

theorem augTensorLeft_comm₂₃ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    (φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)) ≫ (A' ◁ augX B') = (A ◁ augX B) ≫ (φ ⊗ₘ ψ) := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp [TensorProduct.tmul_zero]
    | tmul x b =>
      change φ.hom a ⊗ₜ[k] (augX B').hom (x ⊗ₜ[k] ψ.hom b) =
        φ.hom a ⊗ₜ[k] ψ.hom ((augX B).hom (x ⊗ₜ[k] b))
      rw [augX_tmul, augX_tmul, map_smul]
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add] at hs ht ⊢; rw [hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

noncomputable def augTensorRightMap {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augSES k G).obj A).map (tensorRight B) ⟶ ((augSES k G).obj A').map (tensorRight B') where
  τ₁ := (augIdeal k G ◁ φ) ⊗ₘ ψ
  τ₂ := (Rep.leftRegular k G ◁ φ) ⊗ₘ ψ
  τ₃ := φ ⊗ₘ ψ
  comm₁₂ := augTensorRight_comm₁₂ φ ψ
  comm₂₃ := augTensorRight_comm₂₃ φ ψ

noncomputable def augTensorLeftMap {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((augSES k G).obj B).map (tensorLeft A) ⟶ ((augSES k G).obj B').map (tensorLeft A') where
  τ₁ := φ ⊗ₘ (augIdeal k G ◁ ψ)
  τ₂ := φ ⊗ₘ (Rep.leftRegular k G ◁ ψ)
  τ₃ := φ ⊗ₘ ψ
  comm₁₂ := augTensorLeft_comm₁₂ φ ψ
  comm₂₃ := augTensorLeft_comm₂₃ φ ψ

theorem tδ_map_apply {S₁ S₂ : ShortComplex (Rep.{u} k G)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (F : S₁ ⟶ S₂) (i : ℤ) (x : tateCohomology S₁.X₃ i) :
    (tδ h₂ i (i + 1) rfl).hom (((tateCohomologyFunctor i).map F.τ₃).hom x) =
      ((tateCohomologyFunctor (i + 1)).map F.τ₁).hom ((tδ h₁ i (i + 1) rfl).hom x) :=
  congr(($(TateCohomology.δ_naturality h₁ h₂ F i)).hom x).symm

theorem tateIsoH_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (n : ℕ) [NeZero n]
    (x : tateCohomology X n) :
    (tateIsoH Y n n rfl).hom.hom (((tateCohomologyFunctor n).map φ).hom x) =
      groupCohomology.map (MonoidHom.id G) φ n ((tateIsoH X n n rfl).hom.hom x) :=
  congr(($((TateCohomology.isoGroupCohomology n).hom.naturality φ)).hom x)

end Naturality

end GroundTheory.GroupCoh
