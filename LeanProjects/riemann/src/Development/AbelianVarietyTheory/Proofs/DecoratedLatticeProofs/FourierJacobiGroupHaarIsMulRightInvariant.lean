import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.JacUnimod

theorem jacGrp_rightInv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ ρ d μ hμ
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V₀
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  obtain ⟨hlc, hsc, hbor, hcount⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨ν, 𝓝, hνH, h𝓝, h𝓝1⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  have hnorm := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d
  have hp := GlobalTheory.JacProj.exists_continuous_proj D V V₀ ρ d
  have hc := GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D V V₀ ρ d ν hνH
  let μ₀ : Measure (GA D V₀) := Measure.haar
  have hμ₀ : μ₀.IsHaarMeasure := inferInstance
  haveI := hνH
  haveI : μ₀.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V₀ μ₀ hμ₀
  haveI : ν.IsMulRightInvariant := GlobalTheory.SemiHaar.rightInv_of_fd _ ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed hnorm hp μ₀ ν hμ₀ hνH hc
  obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed hnorm hp
    μ₀ ν hμ₀ hνH hc
  have hH : (semiMeas (flagN d) d.emb0 μ₀ ν).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) d.emb0 hNc d.continuous_embed hnorm μ₀ ν
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) d.emb0 hnorm d.continuous_embed hp
  haveI : LocallyCompactSpace (jacGrp d) := e.symm.isClosedEmbedding.locallyCompactSpace
  let κ : Measure (jacGrp d) := semiMeas (flagN d) d.emb0 μ₀ ν
  haveI hκH : κ.IsHaarMeasure := hH
  haveI hκR : κ.IsMulRightInvariant := hR
  have hk := Measure.isMulLeftInvariant_eq_smul μ κ
  rw [hk]
  infer_instance

end GlobalTheory.JacUnimod

end
