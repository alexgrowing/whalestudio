import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselMoveGap

open GlobalTheory.BesselMove

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_move_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  intro _ k r Wp _ _ _ _ z π u c μW μN μG νq t ht hN hc hψ hS
  obtain ⟨s1, s2, s3, s4, hW, hμN, hG, hq⟩ := hS
  have hti : t⁻¹⁻¹ = t := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of ht))
  have hcan : ∀ n : MM k r, t * (t⁻¹ * n * t) * t⁻¹ = n := fun n => by
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  have hN' : ∀ n ∈ Nset k r, t⁻¹ * n * t ∈ Nset k r := fun n hn => by
    rw [hN, hcan]; exact hn
  have hc' : ∀ h ∈ UWset k r z, t⁻¹ * h = h * t⁻¹ := fun h hh => by
    calc t⁻¹ * h = t⁻¹ * (h * t) * t⁻¹ := by simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      _ = h * t⁻¹ := by rw [← hc h hh, imc ht]
  refine ⟨⟨s1, s2, s3, s4, hW, haar_conj ht hN hμN, hG, ?_⟩, fun R hR => ⟨fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_⟩⟩
  · have := quot_conj ht hG hq
    rw [← muS_conj ht hW hμN hc] at this
    exact this
  · exact bessel_transport hR ht (fun n hn => (hN n).mp hn) hc hψ hB
  · have h := bessel_transport (ψ' := psi k r z c) hR (inv_mem ht) (fun n hn => by rw [hti]; exact hN' n hn) hc'
      (fun n hn => by rw [hti, hψ _ (hN' n hn), hcan]) hB
    have e : (fun v => B (R.σ t (R.σ t⁻¹ v))) = B := by
      funext v
      rw [← sig_mul hR ht (inv_mem ht), mul_inv' ht, sig_one hR]
    rw [e] at h
    exact h
  · intro l₁ hl x hx v hv
    haveI := hW.1
    haveI := hμN.1
    rw [← (hl.2 _ (sig_sm hR (inv_mem ht) hx) _ (sig_TK hR (inv_mem ht) hv)).2]
    show _ = Formalism.FourierDecayAlt.ThreeDimData.be z cStd π R.σ μW (μN.map (conjE ht)) _ _
    unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [prod_conj ht, integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod hW hμN] with p hp
    show (⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) x⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ =
      (⟪R.σ t⁻¹ v, R.σ (Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t)) (R.σ t⁻¹ x)⟫_ℂ *
        star (psi k r z cStd (t⁻¹ * Matrix.of p.2 * t))) • π (Matrix.of p.1)⁻¹
    rw [hψ _ (hN' _ hp.2), hcan, ← sig_inner hR (inv_mem ht) v,
      ← sig_mul hR (inv_mem ht) (mul_mem' hp.1.1 hp.2.1),
      ← sig_mul hR (mul_mem' hp.1.1 (hN' _ hp.2).1) (inv_mem ht)]
    have e : Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t) * t⁻¹ = t⁻¹ * (Matrix.of p.1 * Matrix.of p.2) := by
      simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← hc' _ hp.1, Matrix.mul_assoc]
    rw [e]

end GlobalTheory.BesselMoveGap

end
