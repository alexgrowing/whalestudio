import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap

noncomputable section

namespace Formalism.MainNotions.S.Pv.AIsL

open Formalism.QuantumDeterminants

theorem aIsL (hJ : PI.BesselMapUniq.BesselMapUniq) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hc : ∀ a, c a ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {B l : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π l)
    (hnz : ∃ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, l x ≠ 0) :
    ∃ c0 : ℂ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = c0 • l v := by
  obtain ⟨x, hx, hlx⟩ := hnz
  obtain ⟨α, β, hαβ, hrel⟩ := hJ k r ε lam H σ z c u Wp π hlam hσ hz hT hc hπ B l hB hl
  have hα : α ≠ 0 := by
    intro h0
    rcases hαβ with h1 | h1
    · exact h1 h0
    · have e := hrel x hx
      rw [h0, zero_smul, zero_add] at e
      exact hlx ((smul_eq_zero.1 e).resolve_left h1)
  refine ⟨-(β / α), fun v hv => ?_⟩
  have e := hrel v hv
  have e2 : α • B v = -(β • l v) := eq_neg_of_add_eq_zero_left e
  calc B v = α⁻¹ • (α • B v) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    _ = α⁻¹ • (-(β • l v)) := by rw [e2]
    _ = (-(β / α)) • l v := by rw [smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]

end Formalism.MainNotions.S.Pv.AIsL
