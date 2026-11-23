import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem absDet_radN (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    ∀ n ∈ radN d, GlobalTheory.RegSW.absDet d n = 1 := by
  intro n hn
  obtain ⟨c, b, hcb⟩ := hn
  have hX : mt B (n : GA D B) ⬝ d.jX = d.jX := by
    rw [hcb, mt_mul, Matrix.mul_assoc, d.nB_jX, d.nC_jX]
  have hon : GlobalTheory.RegSW.onX d n = 1 := by
    apply Units.ext
    rw [GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d n), hX, d.pX_jX, Units.val_one]
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, hon, map_one]

end GlobalTheory.CompanionTheory.QKAvg
