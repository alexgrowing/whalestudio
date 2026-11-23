import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement

open UpperTheory.Gal.Int.Geo
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem UpperTheory.grpLat_half {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {M : ℕ}
    (hM : 0 < M) (hc : M.Coprime p) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (s₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = M • v)
    (e : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG h₂ (inAf D x) = M • v) →
      ∃ v ∈ LaHat D, L.actG h₁ (inAf D x) = M • v) :
    ∀ v ∈ LaHat D, L.actG (h₁ * h₂⁻¹) v ∈ LaHat D := by
  intro v hv
  obtain ⟨v', hv', e₁⟩ := s₂ v hv
  obtain ⟨x, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D M hM hc v' hv'
  obtain ⟨u, hu, e₃⟩ := e x ⟨v - L.actG h₂ w, sub_mem hv (i₂ w hw), by
    have h : L.actG h₂ v' = L.actG h₂ (inAf D x) + M • L.actG h₂ w := by
      rw [e₂, map_add, map_nsmul]
    rw [smul_sub, ← e₁, h]
    abel⟩
  have e₄ : M • L.actG (h₁ * h₂⁻¹) v = M • (u + L.actG h₁ w) := by
    have h : L.actG h₂⁻¹ (M • v) = v' := by
      rw [← e₁, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [← map_nsmul, map_mul, Module.End.mul_apply, h, e₂, map_add, map_nsmul, e₃, smul_add]
  have e₅ : L.actG (h₁ * h₂⁻¹) v = u + L.actG h₁ w := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at e₄
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hM.ne' : (M : ℚ) ≠ 0) e₄
  rw [e₅]
  exact add_mem hu (i₁ w hw)

theorem UpperTheory.congruenceSubgroup_isLattice_statement :
    GrpLat := by
  intro p _ D G L M hM hc h₁ h₂ i₁ i₂ s₁ s₂ e
  have a := UpperTheory.grpLat_half L hM hc i₁ i₂ s₂ (fun x => (e x).2)
  have b := UpperTheory.grpLat_half L hM hc i₂ i₁ s₁ (fun x => (e x).1)
  refine ⟨fun v hv => ⟨L.actG (h₁ * h₂⁻¹) v - v, sub_mem (a v hv) hv, by simp⟩,
    fun v hv => ⟨L.actG (h₁ * h₂⁻¹)⁻¹ v - v, sub_mem ?_ hv, by simp⟩⟩
  rw [mul_inv_rev, inv_inv]
  exact b v hv
