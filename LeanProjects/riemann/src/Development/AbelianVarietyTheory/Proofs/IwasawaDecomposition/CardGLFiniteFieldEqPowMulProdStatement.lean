import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod : ∀ (k : Type) [Field k] [Fintype k] (r : ℕ), (Nat.card (GL (Fin r) k) : ℝ) = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  first | exact @GlobalTheory.Mem.card_GL_eq_pow_mul_qE | exact GlobalTheory.Mem.card_GL_eq_pow_mul_qE | (intros; apply GlobalTheory.Mem.card_GL_eq_pow_mul_qE <;> assumption)
