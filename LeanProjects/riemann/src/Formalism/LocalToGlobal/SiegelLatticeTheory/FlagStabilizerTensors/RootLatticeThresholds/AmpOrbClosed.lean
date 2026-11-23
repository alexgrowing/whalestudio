import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HzOfInWb
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.GapOfHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NonzeroKFinite
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneThree
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.TableLineDegreeFive
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv

noncomputable section

namespace Formalism.L2.SG.AmpOrbClosed

open Formalism.BasicNotions Formalism.MainNotions.S

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem ampOrb0_of (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl) :
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 0 :=
  Formalism.L2.SG.AmpOrbPf.amplitudeOrbit_of_local D large₂ C' Cl Cg cb Cu cT CT C0 0
    (Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ) Formalism.FourierDecayAlt.P.discrete_series_form_one
    Formalism.FourierDecayAlt.P.admissible_atomic_form_one hKD Formalism.MainNotions.S.Pv.AmpDDPf.nonzero_K_finite hKF Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (fun h1 h2 => Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 h1 h2)
    (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith))

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem ampOrb_of (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (hKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn) :
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  Formalism.L2.SG.AmpOrbPf.amplitudeOrbit_of_local D large₂ C' Cl Cg cb Cu cT CT C0 Cn
    (Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ) Formalism.FourierDecayAlt.P.discrete_series_form_one
    Formalism.FourierDecayAlt.P.admissible_atomic_form_one hKD Formalism.MainNotions.S.Pv.AmpDDPf.nonzero_K_finite hKF Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (fun h1 h2 => Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 Cn h1 h2) hNV

theorem amplitude_K_finite : Formalism.MainNotions.S.Pv.AmpDD.AmpKF :=
  Formalism.MainNotions.S.Pv.AmpDDPf.amplitude_K_finite_decay Formalism.FourierDecayAlt.P.schur_hermitian Formalism.FourierDecayAlt.P.norm_inverse_bound
    Formalism.FourierDecayAlt.P.growth_group_bound Formalism.FourierDecayAlt.P.double_coset_decomposition Formalism.FourierDecayAlt.P.bessel_convergence
    Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance

theorem ampDD_thm : Formalism.MainNotions.S.Pv.AmpDD.AmpDD :=
  Formalism.MainNotions.S.Pv.AmpDDPf.amplitude_orbital_integral Formalism.FourierDecayAlt.P.schur_hermitian Formalism.FourierDecayAlt.P.norm_inverse_bound
    Formalism.FourierDecayAlt.P.growth_group_bound Formalism.FourierDecayAlt.P.double_coset_decomposition Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem ampOrb0 (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl) :
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 0 :=
  ampOrb0_of hJ hKD amplitude_K_finite D large₂ C' Cl Cg cb Cu cT CT C0 hCl

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem ampOrbNV (hJ : PI.BesselMapUniq.BesselMapUniq) (hKD : Formalism.MainNotions.S.Pv.AmpDD.KDense)
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn) :
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  ampOrb_of hJ hKD amplitude_K_finite D large₂ C' Cl Cg cb Cu cT CT C0 Cn hNV

end Formalism.L2.SG.AmpOrbClosed
