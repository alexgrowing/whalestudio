import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixIntegralityFromCompletePoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_integrality_from_complete_points : ∀ (p : ℕ), p.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (p : O) ∈ maximalIdeal O → Cardinal.mk O ≤ Cardinal.continuum → ∀ (B : Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (A V : B.X.Opens) (x : B.X), genericPoint B.X ∈ A → x ∈ V → x ∉ B.gen → ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) Γ(B.X, V ⊓ A)) (ρ : Fin r → Γ(B.X, V ⊓ A)), (∀ (C : SCF p) (w : Sp ↥(intO ↥C.S) ⟶ B.X), ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ (spMap (intO ↥C.S).subtype ≫ w) ⁻¹ᵁ A → ∀ i, ‖valF (spMap (intO ↥C.S).subtype ≫ w) (V ⊓ A) (ρ i)‖ * matNorm (M.map (valF (spMap (intO ↥C.S).subtype ≫ w) (V ⊓ A))) i = 1) → ∃ (V' : B.X.Opens) (h : V' ≤ V) (P : GL (Fin r) Γ(B.X, V')), x ∈ V' ∧ (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) * M.map (resG B.X (inf_le_inf_right A h))) l j = 0) ∧ ∀ j, ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) * M.map (resG B.X (inf_le_inf_right A h))) j j * resG B.X (inf_le_inf_right A h) (ρ j) = 1 := by
  first | exact @GlobalTheory.TriFrame.Near.exists_tri_near_special | exact GlobalTheory.TriFrame.Near.exists_tri_near_special | (intros; apply GlobalTheory.TriFrame.Near.exists_tri_near_special <;> assumption)
