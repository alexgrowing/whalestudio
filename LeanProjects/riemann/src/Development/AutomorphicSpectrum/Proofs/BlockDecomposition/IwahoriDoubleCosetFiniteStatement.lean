import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_double_coset_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w), (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧ IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w a ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | exact GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | (intros; apply GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL <;> assumption)
