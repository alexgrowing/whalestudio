import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerProductFamily_mul_one_det : ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R), kron M * kron M' = kron (fun t => M t * M' t) ∧ kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧ (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  first | exact @GlobalTheory.DefPt.kronFamily_mul_one_det | exact GlobalTheory.DefPt.kronFamily_mul_one_det | (intros; apply GlobalTheory.DefPt.kronFamily_mul_one_det <;> assumption)
