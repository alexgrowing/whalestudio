import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.TBlkEqTFMulProdTV

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem a_pos (d : SD σ) (x : d.G) : 0 < d.a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  rw [d.ok.hgt.val p t hp k hk]
  exact absE_pos _

theorem ht_eq (d : SD σ) (x : d.G) : ((d.Ht x : ℝ) : ℂ) = (d.a x : ℂ) := by
  simp only [SD.Ht]
  rw [Real.coe_toNNReal _ (a_pos d x).le]

theorem isCompact_K (d : SD σ) : IsCompact (d.K : Set d.G) :=
  SecA.isCompact_stdK' d.B d.Y d.ok.good d.b d.K d.ok.stdK

theorem isClosed_siegel_stabiliser (d : SD σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have e : (par2 σ d.Y : Set d.G) = (fun p : d.G => (inFrame d.b p).toBlocks₂₁) ⁻¹' {0} := by
    ext p
    exact mem_stabiliser_iff_lower_block_zero d.ok.frame p
  rw [e]
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  exact isClosed_singleton.preimage
    (continuous_pi fun i => continuous_pi fun j => hfr.matrix_elem (Sum.inr i) (Sum.inl j))

theorem continuous_a (d : SD σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (isClosed_siegel_stabiliser d) (isCompact_K d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, SecA.uDet_eq ht]

end PositivityTheory.SiegelWeilFormula.kunf

end
