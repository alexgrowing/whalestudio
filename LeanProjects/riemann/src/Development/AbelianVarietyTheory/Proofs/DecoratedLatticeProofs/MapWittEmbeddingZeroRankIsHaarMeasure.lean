import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HaarEmb

theorem map_wittEmbedding_zero_rank_isHaarMeasure : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)), μ.IsHaarMeasure → (Measure.map d.emb0 μ).IsHaarMeasure := by
  intro D S S₀ d μ hμ
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S₀) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D S₀) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hbkc : Continuous (GlobalTheory.WeilSrc.Zero.back d) := continuous_of_mt S₀ (by
    simp only [GlobalTheory.WeilSrc.Zero.back, mt_ofMat]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)
  have hli : ∀ g, GlobalTheory.WeilSrc.Zero.back d (d.emb0 g) = g := fun g =>
    d.wittDecomp_anisotropicEmbedding_injective (GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d _)
  let e : GA D S₀ ≃* GA D S :=
    { toFun := d.emb0, invFun := GlobalTheory.WeilSrc.Zero.back d, left_inv := hli,
      right_inv := GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d, map_mul' := fun x y => map_mul d.emb0 x y }
  exact MulEquiv.isHaarMeasure_map μ e d.continuous_embed hbkc

end GlobalTheory.HaarEmb
