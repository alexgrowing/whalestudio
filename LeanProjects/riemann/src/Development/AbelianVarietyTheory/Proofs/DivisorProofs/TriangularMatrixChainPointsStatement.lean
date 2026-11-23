import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularMatrixChainPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_matrix_chain_points : ∀ (X : Scheme.{0}) (A V V' : X.Opens) (h : V' ≤ V) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s) (e : Fin r → Γ(F, V)) (he : IsFrame e) (P : GL (Fin r) Γ(X, V')) (ρ : Fin r → Γ(X, V' ⊓ A)), (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h))) l j = 0) → (∀ j, ((P : Matrix (Fin r) (Fin r) Γ(X, V')).map (resG X (inf_le_left : V' ⊓ A ≤ V')) * (Matrix.of (GlobalTheory.ChainPts.coef false he hs)).map (resG X (inf_le_inf_right A h))) j j * ρ j = 1) → ∃ e' : Fin r → Γ(F, V'), IsFrame e' ∧ IsTri hs e' ∧ ∀ i, coordIn hs e' i i = ρ i := by
  first | exact @GlobalTheory.TriFrame.exists_isTri_of_mul_coef | exact GlobalTheory.TriFrame.exists_isTri_of_mul_coef | (intros; apply GlobalTheory.TriFrame.exists_isTri_of_mul_coef <;> assumption)
