import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleEigenspaceSup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_irreducible_eigenspace_sup : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' →
    ∀ (r : Fin R) (s : Fin S), GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≤ ⨆ n : ℕ × ℕ,
      Module.End.eigenspace (Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inl r) (.inl r))) (((P : ℂ) - Q) / 2 + n.1) ⊓
      Module.End.eigenspace (Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inr s) (.inr s))) (-(((P : ℂ) - Q) / 2) + n.2) := by
  first | exact @GlobalTheory.FockLowWt.lowOne_le_wt | exact GlobalTheory.FockLowWt.lowOne_le_wt | (intros; apply GlobalTheory.FockLowWt.lowOne_le_wt <;> assumption)
