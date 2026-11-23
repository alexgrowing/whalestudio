import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DSApply
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv ContDiff Matrix Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Lie

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem conj_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w y) =
      InfinitePlace.Completion.extensionEmbedding w y := by
  refine InfinitePlace.Completion.induction_on w y ?_ ?_
  · exact isClosed_eq
      (Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous)
      (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · intro a
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have h := RingHom.congr_fun (InfinitePlace.isReal_iff.mp hw) ((WithAbs.equiv _) a)
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using h

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = (starRingEnd ℂ) (piInf τ x) := by
  obtain ⟨hF, -, -, hστ⟩ := h
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]
    rw [hστ]
    have hc := conj_extensionEmbedding_of_isReal (hF.isReal w) ((evInf F w) a)
    erw [hc]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.infEmb, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
