import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameLastRow

open Topology Filter

theorem lastRow_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (τ₁ : E →+* ℂ), τ₁ ∈ X.Ψ → ∀ (i : ℕ), X.p0 + i + 1 = r → ∃ κ : Frame X.Ψ r → Fin r → ℂ,
      ContinuousOn κ X.dom ∧ (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧
      ∀ x ∈ X.dom, ∀ v, Formalism.L2.PjFree.perFr X x v τ₁ i = κ x ⬝ᵥ Data.emb τ₁ v := by
  intro E _ _ _ r X τ₁ h i hi
  classical
  have hj : X.p0 + i < r := by omega
  let k : X.Ψ := ⟨τ₁, h⟩
  let j : Fin r := ⟨X.p0 + i, hj⟩
  have hm : Continuous (fun x : Frame X.Ψ r => mat x k) := continuous_apply k
  refine ⟨fun x => (mat x k)⁻¹ j, ?_, ?_, ?_⟩
  · intro x hx
    have hd : (mat x k).det ≠ 0 := (hx k).1
    have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x k).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd
    have hinv : ContinuousAt (fun x : Frame X.Ψ r => (mat x k)⁻¹) x :=
      ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x k) (continuousAt_matrix_inv _ hr) hm.continuousAt
    exact ((continuous_apply j).continuousAt.comp hinv).continuousWithinAt
  · intro O hO hOd x hx ξ
    have hd : (mat x k).det ≠ 0 := (hOd hx k).1
    let y : Matrix (Fin r) (Fin r) ℂ := (mat x k)⁻¹
    let Y : ℂ → Matrix (Fin r) (Fin r) ℂ := fun t => y + t • Matrix.of (fun a b => if a = j then ξ b else 0)
    have hYc : Continuous Y := continuous_const.add (continuous_id.smul continuous_const)
    have hY0 : Y 0 = y := by simp [Y]
    have hdy : y.det ≠ 0 := by
      simp only [y, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero hd
    have hYinv : ContinuousAt (fun t => (Y t)⁻¹) 0 := by
      have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (Y 0).det := by
        rw [Ring.inverse_eq_inv', hY0]; exact continuousAt_inv₀ hdy
      exact ContinuousAt.comp (f := Y) (continuousAt_matrix_inv _ hr) hYc.continuousAt
    let xt : ℂ → Frame X.Ψ r := fun t => Function.update x k (fun a b => (Y t)⁻¹ a b)
    have hxt0 : xt 0 = x := by
      have e : (fun a b => (Y 0)⁻¹ a b) = x k := by
        rw [hY0]
        simp only [y]
        rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)]
        rfl
      simp only [xt]
      rw [e]
      exact Function.update_eq_self k x
    have hxtc : ContinuousAt xt 0 := ContinuousAt.update continuousAt_const k hYinv
    have h1 : ∀ᶠ t in 𝓝 (0 : ℂ), xt t ∈ O :=
      hxtc.preimage_mem_nhds (by rw [hxt0]; exact hO.mem_nhds hx)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), (Y t).det ≠ 0 :=
      hYc.matrix_det.continuousAt.eventually_ne (by rw [hY0]; exact hdy)
    filter_upwards [nhdsWithin_le_nhds (h1.and h2)] with t ht
    refine ⟨xt t, ht.1, ?_⟩
    have e : mat (xt t) k = (Y t)⁻¹ := by
      ext a b
      simp [xt, mat]
    show (mat (xt t) k)⁻¹ j = (mat x k)⁻¹ j + t • ξ
    rw [e, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht.2)]
    ext b
    simp [Y, y, j]
  · intro x _ v
    unfold Formalism.L2.PjFree.perFr
    rw [dif_pos h, dif_pos hj]
    rfl

end GlobalTheory.FrameLastRow
