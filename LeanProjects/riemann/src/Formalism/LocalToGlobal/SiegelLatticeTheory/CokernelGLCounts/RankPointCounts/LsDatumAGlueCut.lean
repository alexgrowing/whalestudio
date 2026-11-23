import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def ThL (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  t.abelian₂ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O

def ThSharp (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Submodule M.L.O V where
  carrier := {w | w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDW (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Type :=
  ↥(ThSharp H t N) ⧸ N.comap (ThSharp H t N).subtype

def dwMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (w : ↥(ThSharp H t N)) : DDW H t N :=
  Submodule.Quotient.mk w

end GDefs

section GProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def CorrIso (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∃ ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 f₂ f₂'), (∀ x y, H.h (ψ x) (ψ y) = H.h x y) ∧
      ∀ n₁ n₂ : V, Corr H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' n₁ n₂ ↔
        ∃ h₁ : n₁ ∈ H.W0 t₁.f t₁.f', (ψ ⟨n₁, h₁⟩ : V) = n₂

def GlueEta (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    ∃ η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t),
      (∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂) ∧
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w → η (ddMk H t m') = dwMk H t _ w' →
          H.h m m' + H.h w w' ∈ M.L.O)

def GlueConv (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    IsUnit (H.gram (H.MMfam t)).det → MMInt H t →
    ∀ N : Submodule M.L.O V, N ≤ (H.W0 t.f t.f').restrictScalars M.L.O → N.FG →
      Submodule.span E (N : Set V) = H.W0 t.f t.f' → (∀ x ∈ N, ∀ y ∈ N, H.h x y ∈ M.L.O) →
    ∀ η : DDt H t ≃ₗ[M.L.O] DDW H t N,
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t N)),
        η (ddMk H t m) = dwMk H t N w → η (ddMk H t m') = dwMk H t N w' → H.h m m' + H.h w w' ∈ M.L.O) →
      ∃! Λ : Submodule M.L.O V, H.IsSelfDual Λ ∧ H.Prim Λ (H.MMfam t) ∧
        Λ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O = N ∧
        ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t N)), η (ddMk H t m) = dwMk H t N w ↔ (m : V) + w ∈ Λ

def GenOfPrim (M : Model F E) (r n : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∀ Λ₂ : Submodule M.L.O V, H.IsSelfDual Λ₂ → H.Prim Λ₂ (H.MMfam ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩) →
      H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩

end GProps

end Formalism.L2.SG.LsDatumA
