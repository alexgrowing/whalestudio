import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Tr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def conjHomeomorphOfUnitDet (P : Mat k r) (hu : IsUnit P.det) : Mat k r ≃ₜ Mat k r where
  toFun x := P⁻¹ * x * P
  invFun y := P * y * P⁻¹
  left_inv x := by
    have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h2]; simp
  right_inv y := by
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [h1]; simp
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def cayleyEmbedding (P : Mat k r) (g : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r := P⁻¹ * umat g * P

theorem cayleyEmbedding_measurable {P : Mat k r} (hP : IsCayleyU k r ε P) : MeasurableEmbedding (cayleyEmbedding (ε := ε) P) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (conjHomeomorphOfUnitDet P hu) (umat g)) :=
    (conjHomeomorphOfUnitDet P hu).isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  have h2 : Topology.IsClosedEmbedding (cayleyEmbedding (ε := ε) P) := h1
  exact h2.measurableEmbedding

theorem cayleyEmbedding_mem_unitary {P : Mat k r} (hP : IsCayleyU k r ε P) (g : Formalism.REAL.UJ ε) :
    Matrix.of (cayleyEmbedding P g) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
  show (P⁻¹ * umat g * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * umat g * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hH]
  calc (P⁻¹ * umat g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * umat g * P)
      = Pᴴ * ((umat g)ᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * umat g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((umat g)ᴴ * Formalism.REAL.Jm ε * umat g) * P := by rw [h2]; simp
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [hg]

theorem cayleyEmbedding_map_haar {P : Mat k r} (hP : IsCayleyU k r ε P) :
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (cayleyEmbedding P)) := by
  have hemb := cayleyEmbedding_measurable hP
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne (Formalism.REAL.muG ε)) h0
  · rw [hemb.map_apply]
    have : cayleyEmbedding P ⁻¹' {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = (∅ : Set (Formalism.REAL.UJ ε)) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact cayleyEmbedding_mem_unitary hP g
    rw [this, measure_empty]
  · intro s hs
    have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
      unfold Formalism.QuantumDeterminants.lmulM
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ fun l _ => ?_
      have h0 : Measurable fun x : Formalism.QuantumDeterminants.Mt k r => x l j := by fun_prop
      exact h0.const_mul _
    rw [Measure.map_map hm hemb.measurable]
    set s' : Formalism.REAL.UJ ε := Formalism.REAL.indefiniteUnitaryMk ε (P * s * P⁻¹) (cayley_conj_mem_diagonal_model hP hs).1 with hs'
    have hcomp : Formalism.QuantumDeterminants.lmulM s ∘ cayleyEmbedding (ε := ε) P = cayleyEmbedding P ∘ fun g => s' * g := by
      funext g
      show s * (P⁻¹ * umat g * P) = P⁻¹ * (P * s * P⁻¹ * umat g) * P
      calc s * (P⁻¹ * umat g * P) = (P⁻¹ * P) * s * (P⁻¹ * umat g * P) := by rw [h1]; simp
        _ = P⁻¹ * (P * s * P⁻¹ * umat g) * P := by simp only [Matrix.mul_assoc]
    rw [hcomp, ← Measure.map_map hemb.measurable (measurable_const_mul s'), map_mul_left_eq_self]

theorem haar_eq_smul_cayley_image {P : Mat k r} (hP : IsCayleyU k r ε P) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • (Formalism.REAL.muG ε).map (cayleyEmbedding P) := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, a1, a2, e1⟩ := left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ
  obtain ⟨c2, b1, b2, e2⟩ := left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν (cayleyEmbedding_map_haar hP)
  refine ⟨c1 / c2, ENNReal.div_ne_zero.2 ⟨a1, b2⟩, ENNReal.div_ne_top a2 b1, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel b1 b2]

end Tr

end Formalism.MainNotions.LeviCoordinates

end
