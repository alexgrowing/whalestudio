import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionDilationExp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IsParOfFrame

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem a_dil {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  obtain ⟨hc, hfr⟩ : ∃ hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ, GlobalTheory.ThK.Dbl.inFrame d.b ((R.ι w) y) =
      Matrix.fromBlocks (↑(dilT hc w i₀ τ)) 0 0 ↑(dilT hc w i₀ (-τ)) :=
    ⟨_, inFrame_dil' R w i₀ τ y hy⟩
  obtain ⟨t, ht, hdet⟩ := PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame d (R.ι w y)
    (by rw [hfr, Matrix.toBlocks_fromBlocks₂₁])
  refine ⟨?_, ?_⟩
  · rw [PositivityTheory.SiegelWeilFormula.Avac.a_mul_par d ht h]
    congr 1
    have hdt : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det (dilT hc w i₀ τ) := by
      ext
      rw [hdet, hfr, Matrix.toBlocks_fromBlocks₁₁, Matrix.GeneralLinearGroup.val_det_apply]
    rw [hdt, det_dilT]
    exact absE_adrU hc w τ
  · obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p t' hp k hk]
    exact NNReal.coe_nonneg _

end PositivityTheory.SiegelWeilFormula.AStep

end
