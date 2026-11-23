import Formalism.LocalToGlobal.ClassRec

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

def TSelF {eps : ℝ} (Fm : FamP eps) : Type _ :=
  Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RecT (Fm.ex x hx i)

def TSel (𝒞 : FamClass) : Type _ := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TSelF Fm

theorem TSelF.tiedRec {eps : ℝ} {Fm : FamP eps} (s : TSelF Fm) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TiedRec (Fm.ex x hx i) :=
  ⟨s.1, fun x hx h i => ⟨s.2 x hx h i⟩⟩

def thresholdSelection : TSel LayerTwoFamilyClass := fun _ h =>
  ⟨Classical.choose h.1, fun x hx h0 i => Classical.choice (Classical.choose_spec h.1 x hx h0 i)⟩

def TSel.ofSub {𝒞 : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → LayerTwoFamilyClass Fm) : TSel 𝒞 := fun Fm h => thresholdSelection Fm (hs Fm h)

end Formalism.L2

end
