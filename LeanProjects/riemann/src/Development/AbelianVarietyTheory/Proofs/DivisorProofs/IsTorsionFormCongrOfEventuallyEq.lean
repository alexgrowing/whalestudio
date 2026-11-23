import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open GlobalTheory.TorsionForm

namespace GlobalTheory.TorsionGerm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  {τ τ' : E → Matrix (Fin g) (Fin g) ℂ}

section Deriv

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [SMul ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [SMul ℂ W]

theorem d10_congr {f f' : V → W} {P : V} (hf : f =ᶠ[𝓝 P] f') (v : V) :
    d10 f P v = d10 f' P v := by
  unfold d10; rw [hf.fderiv_eq]

theorem d01_congr {f f' : V → W} {P : V} (hf : f =ᶠ[𝓝 P] f') (v : V) :
    d01 f P v = d01 f' P v := by
  unfold d01; rw [hf.fderiv_eq]

end Deriv

theorem hor_congr {P : Pt E g} (hτ : τ =ᶠ[𝓝 P.1] τ') (v : E) : hor τ P v = hor τ' P v := by
  have e : flat τ P = flat τ' P := by
    unfold flat; rw [hτ.eq_of_nhds]
  have e2 : (fun b => per (τ b) (flat τ P)) =ᶠ[𝓝 P.1] fun b => per (τ' b) (flat τ' P) := by
    filter_upwards [hτ] with b hb
    rw [hb, e]
  unfold hor; rw [e2.fderiv_eq]

theorem imPart_congr {b : E} (hτ : τ b = τ' b) : imPart τ b = imPart τ' b := by
  unfold imPart; rw [hτ]

theorem connForm_congr {b : E} (hτ : τ =ᶠ[𝓝 b] τ') (v : E) (w : Ext (n + n + g)) :
    connForm τ b v w = connForm τ' b v w := by
  have e : ∀ a c, d01 (fun b' => imPart τ b' a c) b v = d01 (fun b' => imPart τ' b' a c) b v := by
    intro a c
    refine d01_congr ?_ v
    filter_upwards [hτ] with x hx
    rw [imPart_congr hx]
  unfold connForm
  simp only [e, imPart_congr hτ.eq_of_nhds]

theorem nab10_congr (h : Pt E g → ℝ) {s s' : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hs : s =ᶠ[𝓝 P] s') (v : Pt E g) : pointDifference h s P v = pointDifference h s' P v := by
  unfold pointDifference; rw [d10_congr hs, hs.eq_of_nhds]

theorem superconn_congr (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {s s' : Pt E g → Ext (n + n + g)} {P : Pt E g} (hτ : τ =ᶠ[𝓝 P.1] τ') (hs : s =ᶠ[𝓝 P] s') :
    superconn τ h β u s P = superconn τ' h β u s' P := by
  unfold superconn nablaE dbarV dbarAdj
  simp only [hor_congr hτ, connForm_congr hτ, nab10_congr h hs, d01_congr hs, hs.eq_of_nhds,
    imPart_congr hτ.eq_of_nhds]

theorem curv_congr (h : Pt E g → ℝ) (β : Fin n → E) {b : E} (hτ : τ =ᶠ[𝓝 b] τ') (u : ℝ) :
    curv τ h β b u = curv τ' h β b u := by
  funext f z
  unfold curv
  refine superconn_congr h β u hτ ?_
  have h1 : ∀ᶠ P : Pt E g in 𝓝 (b, z), τ =ᶠ[𝓝 P.1] τ' :=
    (continuous_fst.tendsto ((b, z) : Pt E g)).eventually hτ.eventuallyEq_nhds
  filter_upwards [h1] with P hP
  exact superconn_congr h β u hP EventuallyEq.rfl

theorem isTorsionForm_congr (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ)
    (τ τ' : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (T : Ext (n + n)) (hτ : τ =ᶠ[𝓝 b] τ')
    (H : IsTorsionForm τ M j h β b T) : IsTorsionForm τ' M j h β b T := by
  have e0 : τ b = τ' b := hτ.eq_of_nhds
  have e1 := curv_congr h β hτ
  unfold IsTorsionForm IsHeatTrace IsHeatKernel IsSec at H ⊢
  simp only [e0, e1] at H
  exact H

end GlobalTheory.TorsionGerm
