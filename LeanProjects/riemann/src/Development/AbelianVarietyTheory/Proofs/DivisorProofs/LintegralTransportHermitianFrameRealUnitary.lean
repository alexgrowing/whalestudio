import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

theorem secondCountable_GL_complex (r : ℕ) : SecondCountableTopology (GL (Fin r) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  have : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountable_Upq (r p : ℕ) : SecondCountableTopology (Upq r p) := by
  have := secondCountable_GL_complex r
  exact TopologicalSpace.Subtype.secondCountableTopology _

theorem sigmaFinite_haarU (r p : ℕ) : SigmaFinite (haarU r p) := by
  have := secondCountable_Upq r p
  unfold haarU
  infer_instance

theorem lintegral_pi_haarU_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (r p q : ℕ) (h : p = q)
    (F : (ι' → Matrix (Fin r) (Fin r) ℂ) → ℝ≥0∞) :
    ∫⁻ g : ι → Upq r p, F (fun i' => ((g (e.symm i') : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r p) =
      ∫⁻ g : ι' → Upq r q, F (fun i' => ((g i' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        ∂Measure.pi (fun _ => haarU r q) := by
  subst h
  have := sigmaFinite_haarU r p
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => haarU r p) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  funext g
  congr 1
  funext i'
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem trF_frameOf {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E']
    [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ) (g : RealGrp X) :
    trF X X' e (frameOf X g) = rmul (baseFr X')
      (fun τ' => (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  funext τ'
  have h : (mat (baseFr X) (e.symm τ')).det ≠ 0 := (X.signature (e.symm τ')).choose_spec.1
  show mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ *
      (mat (baseFr X) (e.symm τ') * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
    mat (baseFr X') τ' * (((g (e.symm τ') : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (mat (baseFr X) (e.symm τ')), Matrix.nonsing_inv_mul _ h.isUnit,
    Matrix.one_mul]

theorem lintegral_trF_frameOf : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  simp_rw [trF_frameOf]
  exact lintegral_pi_haarU_reindex e r X.p0 X'.p0 hp (fun M => φ (rmul (baseFr X') M))

end GlobalTheory.FlagQuotHaar
