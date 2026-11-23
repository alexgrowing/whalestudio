import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeValueEqHilbertEisensteinValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterDEqOfEventuallyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivConstMulReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeEqHilbertEisensteinJetStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.HilbFam

theorem iterD_defSum_eq_jet : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hg hu
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (FR E →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]; omega
    exact ⟨e.symm (NumberField.ComplexEmbedding.IsReal.embedding
      (IsTotallyReal.complexEmbedding_isReal σ))⟩
  set W : (Emb (FR E) → ℂ) → ℂ := fun w ↦ (cK (FR E) (2 * s) : ℂ) *
    gval (2 * s) L (fun j ↦ (τ : ℂ) + w j * (1 * (τ : ℂ) + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + w j * 1) with hW
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : g =ᶠ[nhds 0] fun z ↦ (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * W (fun j ↦ z (e.symm j)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : I → ℂ) one_pos] with z hz
    have hzp : z ∈ polydisc I := fun i ↦ by
      have := norm_le_pi_norm z i
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt this hz
    obtain ⟨G, hG, hgz⟩ := hg z hzp
    have hv := GlobalTheory.T.deformedLattice_value_eq_hilbertEisenstein_value E I φ e θ τ Λ L n (2 * s) z G hI ⟨s, two_mul s⟩ hφ hθ hn hLΛ hG
    have hu' := GlobalTheory.HilbFam.gval_eq_of_isGVal (FR E) (2 * s) L _ _ _ hv
    simp only [hW]
    rw [hu', hgz]
    have : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) = (cK (FR E) (2 * s) : ℂ) := rfl
    rw [this, inv_pow, ← pow_mul, mul_comm (Module.finrank ℚ (FR E)) (2 * s)]
    have h1 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ hn0
    rw [mul_left_comm, mul_inv_cancel_left₀ h1]
  rw [GlobalTheory.HilbFam.iterD_eq_of_eventuallyEq I u g _ 0 key, GlobalTheory.HilbFam.iterD_const_mul_reindex I (Emb (FR E)) e u W _ 0]
  congr 1
  have hc : ∀ j, (u.map e).count j = κ (e.symm j) := fun j ↦ by
    rw [← hu (e.symm j)]
    conv_lhs => rw [← e.apply_symm_apply j]
    convert List.count_map_of_injective u e e.injective (e.symm j)
  have := GlobalTheory.T.iterated_derivative_eq_hilbert_eisenstein_jet hE (FR E) hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) (fun j ↦ κ (e.symm j)) (u.map e) τ.im_pos hc
  exact this

end GlobalTheory.HilbFam
