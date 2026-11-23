import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem integral_leftMul_eq_smul : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)),
    M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ,
      ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  intro D a m n M M' h1 h2
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : SecondCountableTopology (halfMx a m n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hc : ∀ N : Matrix (Fin m) (Fin m) (AE D), Continuous (leftMul a (n := n) N) := fun N =>
    (continuous_const.matrix_mul continuous_subtype_val).subtype_mk _
  let e : halfMx a m n ≃ₜ+ halfMx a m n :=
    { toFun := leftMul a M
      invFun := leftMul a M'
      left_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h2, Matrix.one_mul])
      right_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h1, Matrix.one_mul])
      map_add' := fun x y => Subtype.ext (by
        rw [AddSubgroup.coe_add, leftMul_coe, leftMul_coe, leftMul_coe, AddSubgroup.coe_add, Matrix.mul_add])
      continuous_toFun := hc M
      continuous_invFun := hc M' }
  haveI : ((haarHalf a m n).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarHalf a m n).map e) (haarHalf a m n)
  refine ⟨(Measure.addHaarScalarFactor ((haarHalf a m n).map e) (haarHalf a m n) : ℝ),
    by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun φ => ?_⟩
  let em : halfMx a m n ≃ᵐ halfMx a m n := e.toHomeomorph.toMeasurableEquiv
  have h3 : ∫ t, φ (leftMul a M t) ∂haarHalf a m n = ∫ t, φ t ∂((haarHalf a m n).map e) := by
    have := integral_map_equiv (μ := haarHalf a m n) em φ
    exact this.symm
  have h4 := congrArg (fun μ : Measure (halfMx a m n) => ∫ t, φ t ∂μ) heq
  rw [h3, h4, integral_smul_nnreal_measure]
  simp [Complex.real_smul, NNReal.smul_def]

end GlobalTheory.HalfAverage
