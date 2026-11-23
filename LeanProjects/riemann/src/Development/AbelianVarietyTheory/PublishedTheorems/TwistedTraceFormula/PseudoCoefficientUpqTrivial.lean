import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv

open MeasureTheory GlobalTheory.Orb GlobalTheory.AdelicU Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.Published

def PseudoCoefficientUpq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : GlobalTheory.Dec.IsSqIntIrr ε σ)
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f

theorem PseudoCoefficientUpq.of_isDS (hP : PseudoCoefficientUpq) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (h : IsDS ε lam σ) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure] :
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f :=
  hP n ε X σ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩ μ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult NumberField in

theorem PseudoCoefficientUpq.exists_isTestArchG (hP : PseudoCoefficientUpq) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    [∀ w, (μa w).IsHaarMeasure] : ∃ fa, IsTestArchG M μa fa :=
  GlobalTheory.Orb.exists_isTestArchG M (fun ρ =>
    have ⟨f, hf⟩ := hP.of_isDS (M.ds ρ) (Formalism.REAL.muG _)
    ⟨Formalism.REAL.muG _, inferInstance, f, hf.2⟩) μa

theorem pseudoCoefficientUpq_trivial (n : ℕ) (μ : Measure (Formalism.REAL.UJ (allPos n))) [μ.IsHaarMeasure] :
    ∃ h : GlobalTheory.Dec.IsSqIntIrr (allPos n) (fun _ => ContinuousLinearMap.id ℂ ℂ),
      ∃ f : Formalism.REAL.UJ (allPos n) → ℂ, IsBiFinite (Formalism.REAL.KG (allPos n)) f ∧
        IsPseudoCoeff (ujMat (allPos n)) μ (ujRep h.2.2.1) f := by
  have hJ : Formalism.REAL.Jm (allPos n) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have hK : Formalism.REAL.KG (allPos n) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ⟨?_, by simp [hJ]⟩
    have := g.2
    change _ * _ * _ = _ at this
    rw [hJ, mul_one] at this
    exact Matrix.mem_unitaryGroup_iff'.2 this
  have : CompactSpace (Formalism.REAL.UJ (allPos n)) := by
    have : CompactSpace (Formalism.REAL.KG (allPos n)) := inferInstance
    rw [hK] at this
    exact (Homeomorph.Set.univ _).compactSpace
  refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ => continuousOn_const⟩,
    fun S _ _ => eq_bot_or_eq_top S, fun v w => memLp_const _⟩, fun _ => (μ.real Set.univ : ℂ)⁻¹, ?_, ?_⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ fun _ => (μ.real Set.univ : ℂ)⁻¹) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, -, k', -, rfl⟩
    exact Submodule.mem_span_singleton_self _
  · have := isPseudoCoeff_char (ι := ujMat (allPos n)) (μ := μ) (χ := 1) (isEmbedding_ujMat _).continuous
      ⟨(isClosed_tsupport _).isCompact, fun _ => 1, contDiff_const, fun _ => by simp⟩
    convert this using 1
    · ext g; simp [ujRep, repVia, GlobalTheory.OpTrace.charRep]
    · ext g; simp

end GlobalTheory.Published
