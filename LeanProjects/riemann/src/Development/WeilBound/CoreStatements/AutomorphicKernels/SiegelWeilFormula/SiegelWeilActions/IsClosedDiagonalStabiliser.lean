import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IsClosedSiegelStabiliser
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isClosed_diagonal_stabiliser (d : SD σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have hb := d.ok.frame
  have hset : (par2 σ d.Y : Set d.G) = {p | (inFrame d.b p).toBlocks₂₁ = 0} :=
    Set.ext fun p => mem_stabiliser_iff_frame_lower_block hb p
  rw [hset]
  have hm : Continuous (mat2 (σ := σ) (Y := d.Y)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun p : d.G => inFrame d.b p :=
    (continuous_const.matrix_mul hm).matrix_mul continuous_const
  exact isClosed_eq (continuous_matrix fun i j => hc.matrix_elem (Sum.inr i) (Sum.inl j)) continuous_const

theorem continuous_a' (d : SD σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (isClosed_diagonal_stabiliser d) (kunf.isCompact_K d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (kunf.SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (kunf.SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, kunf.SecA.uDet_eq ht]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
