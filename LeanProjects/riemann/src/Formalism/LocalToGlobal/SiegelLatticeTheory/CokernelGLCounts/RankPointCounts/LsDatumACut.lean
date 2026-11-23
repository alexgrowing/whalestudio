import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAT

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  Submodule.span M.L.O (Set.range (H.MMfam t))

def MMsharp (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V where
  carrier := {u | u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Type :=
  ↥(MMsharp H t) ⧸ (MMo H t).comap (MMsharp H t).subtype

def ddMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (u : ↥(MMsharp H t)) : DDt H t :=
  Submodule.Quotient.mk u

def IsomD (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  ∀ (x y : ↥(MMsharp H t₁)) (x₂ y₂ : ↥(MMsharp H t₂)), θ (ddMk H t₁ x) = ddMk H t₂ x₂ →
    θ (ddMk H t₁ y) = ddMk H t₂ y₂ → H.h x₂ y₂ - H.h x y ∈ M.L.O

def Gam (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)), p = (ddMk H t u, H.mkW t.f ⟨u, hu⟩)}

def Gam' (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f') :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f')), p = (ddMk H t u, H.mkW t.f' ⟨u, hu⟩)}

def GamR (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : E) :
    Set (DDt H t × DDt H t × H.Wb t.f × H.Wb t.f') :=
  {p | ∃ (u u' u'' : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)) (hu' : (u' : V) ∈ H.perp (H.X t.f')),
    (u : V) - u' = c • (u'' : V) ∧
      p = (ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hu⟩, H.mkW t.f' ⟨u', hu'⟩)}

def MMInt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ m ∈ MMo H t, ∀ m' ∈ MMo H t, H.h m m' ∈ M.L.O

def Theta (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Set (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :=
  {θ | IsUnit (H.Dl t₂.f t₂.f' (r + 1)) ∧ MMInt H t₂ ∧ IsomD H t₁ t₂ θ ∧
    (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))}

def LocalCountHypotheses (H : HermSp M V) {r : ℕ} (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') : Prop :=
  H.IsGeneric t₁ ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂ t₁.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂' t₁.T' ∧
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ∧
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) ∧
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r))

end Cut

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def LatSide (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    Nat.card {Λ₂ : Submodule M.L.O V | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'} =
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ')

def ModSide0 (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIso Z₁ Z₂

def ModSideU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = H.ZZplus t₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = H.ZZplus t₁ a.castSucc (Fin.last r) ∧
        (be₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc (Fin.last r) ∧
        (al₁ a : E) = H.ZZplus t₁ (Fin.last r) a.castSucc ∧
        (al₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' (Fin.last r) a.castSucc) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂

theorem localCount_of_lattice_module (M : Model F E) (r n : ℕ) (hL : LatSide M r n) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n := by
  intro V _ _ H hn t₁ hg f₂ f₂' φ φ' hF hF' hI hs hs' S P₁ P₂
  have hT : LocalCountHypotheses H t₁ f₂ f₂' φ φ' := ⟨hg, hF, hF', hI, hs, hs'⟩
  have hLat := hL V H hn t₁ f₂ f₂' φ φ' hT
  refine ⟨fun hD Z₁ Z₂ h₁ h₂ => ?_, fun hD Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba => ?_⟩
  · exact hLat.trans (h0 rfl V H hn t₁ f₂ f₂' φ φ' hT hD Z₁ Z₂ h₁ h₂)
  · exact hLat.trans (hU rfl V H hn t₁ f₂ f₂' φ φ' hT hD Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba)

end Props

end Formalism.L2.SG.LsDatumA
