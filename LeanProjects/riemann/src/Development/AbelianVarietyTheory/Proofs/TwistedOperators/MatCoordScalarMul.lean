import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CentreAvg

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_finite

variable {n : ℕ}

theorem ujMat_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, map_mul,
    show ujMat ε (GlobalTheory.SqIntSU.unitScalar ε z) = (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) from rfl,
    Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem matCoord_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    GlobalTheory.Orb.matCoord (ujMat ε) (scalarMul ε (z, g)) = (z : ℂ) • GlobalTheory.Orb.matCoord (suMat ε) g := by
  funext i j
  simp only [GlobalTheory.Orb.matCoord, ujMat_scalarMul, Pi.smul_apply, Matrix.smul_apply]

theorem avg_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℤ) (f : UJ ε → ℂ), f ∈ CcMat (ujMat ε) →
    (fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) ∈ CcMat (suMat ε) := by
  intro n ε m f hf
  obtain ⟨hc, Φ, hΦ, e⟩ := hf
  refine ⟨?_, fun x => ∫ z, (z : ℂ) ^ m * Φ ((z : ℂ) • x) ∂circleHaar, ?_, ?_⟩
  ·
    let W : Set (UJ ε) := (fun p : Circle × UJ ε => (GlobalTheory.SqIntSU.unitScalar ε p.1)⁻¹ * p.2) '' (Set.univ ×ˢ tsupport f)
    have hW : IsCompact W := (isCompact_univ.prod hc.isCompact).image
      (((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp continuous_fst).inv.mul continuous_snd)
    have hT : IsCompact ((Subtype.val : SUJ ε → UJ ε) ⁻¹' W) :=
      (GlobalTheory.SqIntSU.isClosed_special ε).isClosedEmbedding_subtypeVal.isCompact_preimage hW
    refine HasCompactSupport.intro hT fun g hg => ?_
    have h0 : ∀ z : Circle, f (scalarMul ε (z, g)) = 0 := by
      intro z
      refine image_eq_zero_of_notMem_tsupport fun hz => hg ?_
      refine ⟨(z, scalarMul ε (z, g)), ⟨trivial, hz⟩, ?_⟩
      show (GlobalTheory.SqIntSU.unitScalar ε z)⁻¹ * (GlobalTheory.SqIntSU.unitScalar ε z * (g : UJ ε)) = g
      exact inv_mul_cancel_left _ _
    simp only [h0, zero_mul, integral_zero]
  · have hφ : Continuous fun z : Circle => (z : ℂ) ^ m := by
      have : (fun z : Circle => (z : ℂ) ^ m) = fun z : Circle => ((z ^ m : Circle) : ℂ) := by
        funext z; rw [Circle.coe_zpow]
      rw [this]
      exact continuous_subtype_val.comp (continuous_zpow m)
    have hφc : HasCompactSupport fun z : Circle => (z : ℂ) ^ m :=
      HasCompactSupport.intro isCompact_univ fun x hx => (hx (Set.mem_univ x)).elim
    have hO : @OpensMeasurableSpace Circle _ GlobalTheory.SqIntSU.circleBorelMS :=
      @BorelSpace.opensMeasurable Circle _ GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace
    exact @GlobalTheory.Orb.contDiff_integral_param Circle ℂ (Fin n → Fin n → ℂ) _ GlobalTheory.SqIntSU.circleBorelMS hO _ circleHaar _
      _ _ _ _ _ (fun z : Circle => (z : ℂ)) continuous_subtype_val _ hφ hφc
      (fun q : (Fin n → Fin n → ℂ) × ℂ => Φ (q.2 • q.1)) (hΦ.comp (contDiff_snd.smul contDiff_fst))
  · intro g
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [e, matCoord_scalarMul, mul_comm]

end GlobalTheory.CentreAvg
