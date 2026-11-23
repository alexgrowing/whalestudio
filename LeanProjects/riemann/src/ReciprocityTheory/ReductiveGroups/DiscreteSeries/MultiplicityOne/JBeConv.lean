import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bc_continuous_ell (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ (fun a _ => ?_)
  split_ifs <;> fun_prop

theorem bc_norm_psiD {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  simp [psiD, psi, Complex.norm_exp]

theorem stBeConv (h : UnitaryGroupStructuralFacts) : StBeConv := by
  intro k r Wp _ _ _ D X hD hsq b hb u v ⟨C, hC⟩
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, hCN, hCW, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hint := (stSInt h k r Wp D hD b (bc_AB_le_of b hb)).const_mul C
  set S : Set (Mt k r × Mt k r) := {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
    (Matrix.of p.2 : Mat k r) ∈ Nset k r} with hSdef
  have aeS : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ S :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  have hinvW : ∀ x ∈ UWset k r D.z, x⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem
  have hnorm : ∀ p ∈ S, ‖beInt D X u v p‖ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by
    intro p hp
    have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
    have h1 := hC _ hG
    have hπ : ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
      rw [D.π_unitary _ (hinvW _ hp.1) w, one_mul]
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, bc_norm_psiD, mul_one]
    calc ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖
        ≤ ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hπ (norm_nonneg _)
      _ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by rw [mul_one]; exact h1
  refine Integrable.mono' hint ?_ ?_
  · have cW : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} := (hCW k r D.z).closed
    have cN : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Nset k r} := (hCN k r).closed
    have hSmeas : MeasurableSet S :=
      (cW.measurableSet.preimage measurable_fst).inter (cN.measurableSet.preimage measurable_snd)
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => mc X u v (Matrix.of p.2 * Matrix.of p.1)) S := by
      have hm : ContinuousOn (fun p : Mt k r × Mt k r => X.σ (Matrix.of p.2 * Matrix.of p.1) u) S :=
        (X.rep.2.2 u).comp (bc_continuous_mulM.comp continuous_swap).continuousOn
          (fun p hp => (hCG k r).mul_mem _ hp.2.1 _ hp.1.1)
      exact continuousOn_const.inner hm
    have c2 : Continuous (fun p : Mt k r × Mt k r => star (psiD D (Matrix.of p.2))) := by
      unfold psiD psi
      exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul ((bc_continuous_ell k r D.z).comp continuous_snd)))))).star
    have c3 : ContinuousOn (fun p : Mt k r × Mt k r => D.π (Matrix.of p.1 : Mat k r)⁻¹) S := by
      refine D.π_cont.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) ?_
        (fun p hp => hinvW _ hp.1)
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hdet : (Matrix.of p.1 : Mat k r).det ≠ 0 := ((hCW k r D.z).unit _ hp.1).ne_zero
      have hi : ContinuousAt (fun x : Mat k r => x⁻¹) (Matrix.of p.1) :=
        continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
      exact hi.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) continuous_fst.continuousAt
    have hcont : ContinuousOn (beInt D X u v) S := (c1.mul c2.continuousOn).smul c3
    have hm := hcont.aestronglyMeasurable (μ := D.μW.prod D.μN) hSmeas
    rwa [Measure.restrict_eq_self_of_ae_mem aeS] at hm
  · filter_upwards [aeS] with p hp
    exact hnorm p hp

end ReciprocityTheory.ChartRestriction.DS.Mult1
