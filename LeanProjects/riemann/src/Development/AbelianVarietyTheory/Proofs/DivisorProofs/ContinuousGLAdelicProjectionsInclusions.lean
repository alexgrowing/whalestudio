import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory Matrix

namespace GlobalTheory.GLProj

theorem continuous_proj_incl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧
    Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  intro E _ _ _ a
  have hInf : Continuous (pInf E) :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
  have hFin : Continuous (pFin E) := continuous_snd
  refine ⟨Continuous.units_map _ (continuous_id.matrix_map hInf),
    Continuous.units_map _ (continuous_id.matrix_map hFin), continuous_infGL, ?_⟩
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (sFin E) 1 + x.map (sFin E))

end GlobalTheory.GLProj
