import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendingLetterChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descending_letter_chain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → ∃ (n : ℕ) (u : Fin n → Let Dw.mult) (k : Fin n), Down u ∧ Down (u ∘ Fin.castLE k.2.le) ∧ Down (u ∘ Fin.castLE (Nat.succ_le_of_lt k.2)) ∧ u k = x ∧ ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Sp C ⟶ X) (fr : Vecs Dw t C) (p : ℕ), lnStep t y fr p false st = Real.log (grNorm t y (latDR t y) (fun i => fr (u i).1 (u i).2) k) := by
  first | exact @GlobalTheory.Proof.exists_descending_letter_chain.step_position | exact GlobalTheory.Proof.exists_descending_letter_chain.step_position | (intros; apply GlobalTheory.Proof.exists_descending_letter_chain.step_position <;> assumption)
