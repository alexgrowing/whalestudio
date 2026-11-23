import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ShiftedParametersOfDifferingLetters

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S ContinuousLinearMap
open scoped InnerProductSpace

section Toolkit

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def t76L : (E →L[ℂ] E) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ E) ∘ₗ (ContinuousLinearMap.coeLM ℂ)

def t76 (T : E →L[ℂ] E) : ℝ := (t76L T).re

structure IsOrthogonalProjection (P : E →L[ℂ] E) : Prop where
  idem : P.comp P = P
  sa : adjoint P = P

theorem IsOrthogonalProjection.compl {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) : IsOrthogonalProjection (ContinuousLinearMap.id ℂ E - P) := by
  constructor
  · ext x
    have := congrArg (fun T : E →L[ℂ] E => T x) h.idem
    simp only [ContinuousLinearMap.comp_apply] at this
    simp [this]
  · rw [map_sub, h.sa]
    congr 1
    exact ((eq_adjoint_iff _ _).2 (fun x y => rfl)).symm

theorem IsOrthogonalProjection.norm_le {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have h1 : ⟪P x, P x⟫_ℂ = ⟪x, P x⟫_ℂ := by
    have : ⟪P x, P x⟫_ℂ = ⟪x, (adjoint P) (P x)⟫_ℂ := (adjoint_inner_right P x (P x)).symm
    rw [this, h.sa]
    have h2 := congrArg (fun T : E →L[ℂ] E => T x) h.idem
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h2]
  have h3 : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ := by
    have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
    have h5 : (⟪P x, P x⟫_ℂ).re = ‖P x‖ ^ 2 := by simpa using h4
    rw [← h5, h1]
    exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  by_cases h0 : ‖P x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end Toolkit

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem IsOrthogonalProjection.app {P : E →L[ℂ] E} (h : IsOrthogonalProjection P) (x : E) : P (P x) = P x := by
  have h2 := congrArg (fun T : E →L[ℂ] E => T x) h.idem
  simpa using h2

end Abstract

section CorF

variable {W : Type} {C : W → Type} [∀ u, NormedAddCommGroup (C u)] [∀ u, InnerProductSpace ℂ (C u)]
  [∀ u, FiniteDimensional ℂ (C u)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (Ws : Finset W) (P : ∀ u, C u →L[ℂ] H) (c : W → ℝ) (Pu : ∀ u, C u →L[ℂ] C u) (Pi : H →L[ℂ] H)

def q76 (u : W) : H →L[ℂ] H := (P u).comp ((Pu u).comp (adjoint (P u)))

def weightedProjectionSum : H →L[ℂ] H := ∑ u ∈ Ws, (c u : ℂ) • q76 P Pu u

def gramBlock' (u u' : W) : C u' →L[ℂ] C u := (adjoint (P u)).comp (P u')

def compressedProjectionSum : H →L[ℂ] H :=
  ∑ u ∈ Ws, (c u : ℂ) • (Pi.comp ((P u).comp ((Pu u).comp ((adjoint (P u)).comp Pi))))

variable {P c Pu Pi}

end CorF

section CorFNum

variable {W : Type} {C : W → Type} [∀ u, NormedAddCommGroup (C u)] [∀ u, InnerProductSpace ℂ (C u)]
  [∀ u, FiniteDimensional ℂ (C u)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (Ws : Finset W) {P : ∀ u, C u →L[ℂ] H} {c : W → ℝ} {Pu : ∀ u, C u →L[ℂ] C u} {Pi : H →L[ℂ] H}

end CorFNum

section CorFRecord

variable (D : D7) (large₂ : SizeData₂ D)

end CorFRecord

section CorFFamily

variable {eps : ℝ} (Fm : FamP eps)

end CorFFamily

end Formalism.MainNotions.BridgeLemma

end
