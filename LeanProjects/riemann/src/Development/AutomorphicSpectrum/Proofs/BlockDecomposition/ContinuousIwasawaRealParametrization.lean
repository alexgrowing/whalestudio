import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord

theorem continuous_diagonal_real_torus :
    Continuous (fun q : ℝˣ × ℝˣ => (dg2 q.1 q.2 : GL (Fin 2) ℝ)) := by
  have hv1 : Continuous (fun q : ℝˣ × ℝˣ => (q.1 : ℝ)) := Units.continuous_val.comp continuous_fst
  have hv2 : Continuous (fun q : ℝˣ × ℝˣ => (q.2 : ℝ)) := Units.continuous_val.comp continuous_snd
  have hi1 : Continuous (fun q : ℝˣ × ℝˣ => ((q.1⁻¹ : ℝˣ) : ℝ)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_fst
  have hi2 : Continuous (fun q : ℝˣ × ℝˣ => ((q.2⁻¹ : ℝˣ) : ℝ)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_snd
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : ℝˣ × ℝˣ => (!![(q.1 : ℝ), 0; 0, (q.2 : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using hv1) | (simpa using hv2) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : ℝˣ × ℝˣ =>
      (!![((q.1⁻¹ : ℝˣ) : ℝ), 0; 0, ((q.2⁻¹ : ℝˣ) : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using hi1) | (simpa using hi2) | (simpa using continuous_const)

theorem continuous_iwasawa_coord :
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => dg2 (p.1 * p.2.1) p.2.1 * p.2.2) := by
  have h : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => ((p.1 * p.2.1, p.2.1) : ℝˣ × ℝˣ)) :=
    (continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd)
  exact (continuous_diagonal_real_torus.comp h).mul (continuous_snd.comp continuous_snd)

end GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord
