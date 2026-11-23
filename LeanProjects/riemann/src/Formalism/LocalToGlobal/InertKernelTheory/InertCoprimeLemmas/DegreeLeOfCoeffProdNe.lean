import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgGr
import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.JetsInOfOneVariable
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusExtensionOnInclusion

noncomputable section

namespace Formalism.L2.KerInert

namespace GrP

open MvPowerSeries

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end GrP

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

namespace GrP

open MvPowerSeries Formalism.InvariantFactorPaths.G7

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end GrP

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

namespace GrP

open MvPowerSeries Formalism.InvariantFactorPaths.G7

variable {K : Type} [NormedField K] [IsUltrametricDist K]

section Tri

variable {n : Type} [Fintype n] [DecidableEq n]

end Tri

end GrP

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

namespace GrP

open MvPowerSeries Formalism.InvariantFactorPaths.G7

section Lin

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def lin {m n : Type} [Fintype n] (M : Matrix m n K) (i : m) : MvPowerSeries n K := ∑ j, C (M i j) * X j

end Lin

section Undo

variable (l : ℕ) [Fact l.Prime]

def qF : PowerSeries ℂ_[l] := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (lgF ℂ_[l] l)

end Undo

end GrP

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

namespace GrP

open MvPowerSeries Formalism.InvariantFactorPaths.G7

end GrP

end Formalism.L2.KerInert

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv)

namespace AlgGrP

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem tors_of_torsPrime (B : Ker.Base D cc δ) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (s : Formalism.MainNotions.TaylorLogMetric.VC D N N')
    (hs : Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s)
    (b : Fin N' × Fin N) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ (m : ℂ) • (fun τ => s τ b.1 b.2) ∈ B.lamM := by
  obtain ⟨m, hm, hcop, hms⟩ := hs
  rw [B.lat0OK N N'] at hms
  refine ⟨m, hm, (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).1 hcop.symm, ?_⟩
  have := hms b.1 b.2
  convert this using 1
  funext τ
  simp [nsmul_eq_mul]

theorem U_thZero_algEnt' (h : ThMMTransAlgPrime) (B : Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (N N' : ℕ) (s : Formalism.MainNotions.TaylorLogMetric.VC D N N')
    (hs : Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s) :
    AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor s (B.thZero N N')) := by
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hQ : ∀ b : Fin N' × Fin N, CoefInMv (trM B (fun τ => s τ b.1 b.2) B.thMM) Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro b
    obtain ⟨m, hm, hpm, hms⟩ := tors_of_torsPrime B s hs b
    exact h D cc δ B hcc hδ p hp5 hin _ m hm hpm hms
  have h' := AlgP.coefInMv_prod
    (fun (b : Fin N' × Fin N) (w : D.what₂.Tau × Fin N' × Fin N → ℂ) => trM B (fun τ => s τ b.1 b.2) B.thMM (fun t => w (t, b)))
    (fun b => AlgP.analyticOnNhd_sel _ (AlgP.trM_analytic B hS _) (fun t => (t, b))) Formalism.MainNotions.TaylorLogMetric.Qbar
    (fun b => AlgP.coefInMv_sel _ (AlgP.trM_analytic B hS _) (fun t => (t, b)) _ (hQ b))
  rw [← AlgP.U_thZero_unc] at h'
  exact ⟨AlgP.analytic_of_unc _ h'.2, fun α => AlgP.taylor_mem_of D N N' _ h'.2 _ h'.1 α⟩

theorem algZero_of_transPrime (h : ThMMTransAlgPrime) : AlgZero := by
  intro D cc δ B hcc hδ p _ hp5 hin N N' s hs
  exact U_thZero_algEnt' h B hcc hδ p hp5 hin N N' s hs

theorem algFact_of_transPrime (h : ThMMTransAlgPrime) : AlgFact := by
  intro D cc δ B hcc hδ χ hχ p _ hp5 hin N N'
  have h2 : ∀ s : Formalism.MainNotions.TaylorLogMetric.VC D N N',
      Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
      AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor s (B.thZero N N')) := fun s hs =>
    U_thZero_algEnt' h B hcc hδ p hp5 hin N N' s hs
  refine ⟨fun M M' hA hM hM' t ht => ?_, h2⟩
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  let lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p] := (IsAlgClosed.lift : Formalism.MainNotions.TaylorLogMetric.Qbar →ₐ[ℚ] ℂ_[p]).toRingHom
  obtain ⟨m, c, s, hc, hs, heq⟩ := pairs_standard_at_p D cc δ B hcc hδ χ hχ p hp5 hin lam N N' M M' hA hM hM' t ht
  have hG : ∀ k, AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor (s k) (B.thZero N N')) := fun k => h2 (s k) (hs k)
  rw [heq]
  refine ⟨?_, fun α => ?_⟩
  · intro z _
    have h := Finset.analyticAt_sum (f := fun k w => c k * Formalism.MainNotions.TaylorLogMetric.U D B.tor (s k) (B.thZero N N') w) Finset.univ
      fun k _ => analyticAt_const.mul ((hG k).1 z (Set.mem_univ _))
    rw [Finset.sum_fn] at h
    exact h
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.taylor_lin c _ (fun k m => (hG k).1.contDiff) α]
  exact sum_mem fun k _ => mul_mem (hc k).1 ((hG k).2 α)

end AlgGrP

end Formalism.L2.KerInert
