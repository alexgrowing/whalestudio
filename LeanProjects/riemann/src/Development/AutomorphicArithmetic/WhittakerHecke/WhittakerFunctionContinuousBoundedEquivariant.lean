import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem compact_cover_fundamental_domain : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, Set.pi_mono fun _ _ => hs⟩

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

theorem UpperTheory.whittakerFunction_continuous_bounded_equivariant :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Continuous (Wo D φ) ∧ (∃ B : ℝ, ∀ h, ‖Wo D φ h‖ ≤ B) ∧
        (∀ (u : Fin 2 → A ℚ) h, Wo D φ (nE D u * h) = ψ (-(u 1)) * Wo D φ h) ∧
        (∀ z h, Wo D φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * Wo D φ h) := by
  intro E _ _ D ω φ hφ
  obtain ⟨B, hB⟩ := hφ.bdd
  refine ⟨?_, ⟨B, fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.2 φ B h hB⟩,
    fun u h => UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D φ ⟨hφ.cont, hφ.left⟩ u h, fun z h => ?_⟩
  · obtain ⟨C, hC, hs⟩ := compact_cover_fundamental_domain
    have e : Wo D φ = fun h => ∫ u in C, φ (nE D u * h) * ψ (u 1) ∂((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := by
      funext h
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]
      rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) :=
      ⟨by simpa using (measure_mono hs).trans_lt hC.measure_lt_top⟩
    exact continuous_parametric_integral_of_continuous
      ((hφ.cont.comp (((cont_nE D).comp continuous_snd).mul continuous_fst)).mul
        (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp ((continuous_apply 1).comp continuous_snd))) hC
  · unfold Wo
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only []
    rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc, hφ.cen, mul_assoc]
