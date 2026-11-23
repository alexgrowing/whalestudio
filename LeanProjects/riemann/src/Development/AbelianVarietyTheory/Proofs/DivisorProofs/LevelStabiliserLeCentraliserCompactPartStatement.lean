import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_stabiliser_le_centraliser_compact_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU E n, twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ)) ∧ (twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ))) ≠ 0 := by
  first | exact @GlobalTheory.BCT.CentLev.stab_le_cptPart | exact GlobalTheory.BCT.CentLev.stab_le_cptPart | (intros; apply GlobalTheory.BCT.CentLev.stab_le_cptPart <;> assumption)
