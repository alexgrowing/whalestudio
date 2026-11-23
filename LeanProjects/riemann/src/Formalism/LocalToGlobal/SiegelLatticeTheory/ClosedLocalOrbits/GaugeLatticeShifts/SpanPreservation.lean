import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.RealObj.SpanPreservation

open Formalism.L2.SG.HidaSetting

theorem span_pres {n r : ℕ} (e : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) {y : Fin n → ℂ} (hy : y ∈ spanLt e r) :
    g *ᵥ y ∈ spanLt e r := by
  have hmono : ∀ a : Fin r, spanLt e a.1 ≤ spanLt e r := fun a =>
    Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a.1) => lt_trans hb a.2)
  have hgen : ∀ a : Fin r, g *ᵥ e a ∈ spanLt e r := by
    intro a
    have e1 : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨a, a.2, rfl⟩) (hmono a (hg a))
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem w hw => obtain ⟨b, -, rfl⟩ := hw; exact hgen b
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ ha

theorem inN_inv {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (h1 : gi * g = 1) (hg : InN ε e z g) : InN ε e z gi := by
  have hS : InS e z gi := Formalism.L2.SG.RealObj.InfCut.inS_inv e z g gi h1 hg.1
  refine ⟨hS, fun y hy => ?_⟩
  have key : (gi - 1) *ᵥ y = -(gi *ᵥ ((g - 1) *ᵥ y)) := by
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1]
  rw [key]
  exact Submodule.neg_mem _ (span_pres e gi hS.1 (hg.2 y hy))

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ninfU_inv (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : s⁻¹ ∈ X.NinfU u := fun v =>
  inN_inv _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)) (hs v)

end Formalism.L2.SG.RealObj.SpanPreservation
