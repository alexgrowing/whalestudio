import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchLine

theorem sch_hasDerivAt_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ M : ℝ →+ Mx D B.rank A.rank, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ ∀ x, HasDerivAt (fun t : ℝ => sch ψ A B ν 𝓨 f (x + M t)) (sch ψ A B ν 𝓨 f' x) 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf M hM hMf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let L : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp M
  have hLc : Continuous L := (continuous_id.matrix_mul continuous_const).comp hM
  have hLf : ∀ t, (L t).map (finPart D) = 0 := by
    intro t
    show (((dblDec A).extX B) (M t)).map (finPart D) = 0
    rw [HypDec.extX_apply, Matrix.map_mul, hMf t, Matrix.zero_mul]
  obtain ⟨_, hT⟩ := GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ (dblSp A) B 0 f hf
  obtain ⟨hf', hlim⟩ := hT L hLc hLf
  refine ⟨_, hf', fun x => ?_⟩
  set f' := fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (L t) f p) 0 with hf'def
  obtain ⟨C, hC⟩ := GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) v 0
  have hS := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1
  have hth : ∀ t, IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B (L t) f) := fun t =>
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have lin := GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν

  have htr : ∀ t : ℝ, sch ψ A B ν 𝓨 f (x + M t) = sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x := by
    intro t
    exact (congrFun (hS x (M t)) 0).symm

  have key : ∀ t : ℝ, IsThetaFunO ψ (dblSp A) B ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') ∧
      sch ψ A B ν 𝓨 ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') x =
        (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) - sch ψ A B ν 𝓨 f' x := by
    intro t
    have e : (t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f' =
        ((t⁻¹ : ℂ) • heisO ψ (dblSp A) B (L t) f + (-(t⁻¹ : ℂ)) • f) + (-1 : ℂ) • f' := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h1 := lin _ _ (hth t) hf (t⁻¹ : ℂ)
    have h2 := lin _ _ hf hf (-(t⁻¹ : ℂ))
    have ha := GlobalTheory.OrientedHeis.theta_smul (t⁻¹ : ℂ) (hth t)
    have hb := GlobalTheory.OrientedHeis.theta_smul (-(t⁻¹ : ℂ)) hf
    have hc := GlobalTheory.OrientedHeis.theta_smul (-1 : ℂ) hf'
    have hab := GlobalTheory.OrientedHeis.theta_add ha hb
    rw [e]
    refine ⟨GlobalTheory.OrientedHeis.theta_add hab hc, ?_⟩
    rw [(lin _ _ hab hc 1).2.2.1, (lin _ _ ha hb 1).2.2.1, (lin _ _ (hth t) hf (t⁻¹ : ℂ)).2.2.2,
      (lin _ _ hf hf (-(t⁻¹ : ℂ))).2.2.2, (lin _ _ hf' hf' (-1 : ℂ)).2.2.2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_edist_tendsto_0]
  have hup : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ 0
      ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f')) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => by simp) (fun t => ?_)
  have hb := hC _ (key t).1 x 0
  rw [pow_zero, ENNReal.ofReal_one, mul_one] at hb
  have e2 : t⁻¹ • (sch ψ A B ν 𝓨 f (x + M (0 + t)) - sch ψ A B ν 𝓨 f (x + M 0)) =
      (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) := by
    rw [zero_add, htr t, map_zero, add_zero, Complex.real_smul, Complex.ofReal_inv]
  simp only
  rw [e2, edist_eq_enorm_sub, ← (key t).2]
  exact hb

end GlobalTheory.SchLine
