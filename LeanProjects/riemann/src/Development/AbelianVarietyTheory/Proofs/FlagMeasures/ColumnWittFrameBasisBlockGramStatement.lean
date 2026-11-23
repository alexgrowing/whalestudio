import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnWittFrame_basis_blockGram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  first | exact @GlobalTheory.St.qFrame_basis_gram | exact GlobalTheory.St.qFrame_basis_gram | (intros; apply GlobalTheory.St.qFrame_basis_gram <;> assumption)
