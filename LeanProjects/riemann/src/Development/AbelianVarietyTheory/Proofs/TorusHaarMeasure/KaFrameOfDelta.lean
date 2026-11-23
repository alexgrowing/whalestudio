import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

private theorem lact_rmul_torus_haar_measure {r : ℕ} {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat y τ) (mat b τ)).symm

theorem kaFrame_of_delta {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (hbb : 0 < bb)
    (δ : Frame X.Ψ r → ℝ) (h0 : ∀ x, 0 ≤ δ x) (hm : Measurable δ)
    (hpos : ∀ x ∈ X.dom, 0 < δ x ∧ δ x ≤ 1)
    (hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, δ (rmul x b) = δ x)
    (hch : ∀ z ∈ OmF X x0, δ (cpt X x0 z) = Real.exp (-rhF X x0 z))
    (hloc : ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → δ (cpt X x z) ≤ C * δ x)
    (hsum : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (δ (lact γ.1 x) ^ (bb / 2)) ≤ C) :
    ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧
      (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom,
        ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧
      ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x := by
  have hb0 : 0 ≤ bb := hbb.le
  refine ⟨fun x => δ x ^ bb, hm.pow_const bb, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hpos x hx
    exact ⟨Real.rpow_pos_of_pos h1 bb, Real.rpow_le_one h1.le h2 hb0⟩
  · intro x hx b hb
    show δ (rmul x b) ^ bb = δ x ^ bb
    rw [hinv x hx b hb]
  · intro z hz
    show δ (cpt X x0 z) ^ bb = kaF X x0 bb z
    rw [hch z hz, kaF, ← Real.exp_mul]
    congr 1
    ring
  · obtain ⟨C, hC, hCb⟩ := hsum
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨x1, hx1, b, hb, rfl⟩ := (ortho_holds (E := E)) r X x hx
    have hd1 : x1 ∈ X.dom := IC.orth_mem_dom X hx1
    calc ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (δ (lact γ.1 (rmul x1 b)) ^ bb))
        = ∑' γ : X.Γ, ENNReal.ofReal (δ (lact γ.1 x1) ^ (bb / 2)) := by
          refine tsum_congr fun γ => ?_
          rw [lact_rmul_torus_haar_measure, hinv _ (OntoS.dom_lact X γ.2 hd1) b hb, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (h0 _), show bb / 2 = bb * (1 / 2) by ring]
      _ ≤ C := hCb x1 hx1
  · obtain ⟨ρ, C, hρ, hC⟩ := hloc
    refine ⟨ρ, max C 0 ^ bb, hρ, fun x hx z hz => ?_⟩
    have h1 : δ (cpt X x z) ≤ max C 0 * δ x :=
      (hC x hx z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 x))
    show δ (cpt X x z) ^ bb ≤ max C 0 ^ bb * δ x ^ bb
    calc δ (cpt X x z) ^ bb ≤ (max C 0 * δ x) ^ bb := Real.rpow_le_rpow (h0 _) h1 hb0
      _ = max C 0 ^ bb * δ x ^ bb := Real.mul_rpow (le_max_right _ _) (h0 x)

theorem kaFrame : (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ C * (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal ((∏ τ : X.Ψ, ‖dmin X.Gm (lact γ.1 x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (lact γ.1 x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ^ s) ≤ C) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) := by
  intro hM hL hS r X x0 hx0 hpd bb hbb
  obtain ⟨h1, h2, h3, h4⟩ := hM r X x0 hx0
  have hc : 0 ≤ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
  refine kaFrame_of_delta X x0 bb (by linarith) _ (fun x => Finset.prod_nonneg fun τ _ => by positivity)
    h1 h2 h3 h4 (hL r X x0 hx0) (hS r X x0 hx0 hpd (bb / 2) (by linarith))

end GlobalTheory
