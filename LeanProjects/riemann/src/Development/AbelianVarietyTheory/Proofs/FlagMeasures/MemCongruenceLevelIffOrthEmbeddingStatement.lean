import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCongruenceLevelIffOrthEmbedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruence_level_iff_orthEmbedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf → (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧ ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  first | exact @GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | exact GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | (intros; apply GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb <;> assumption)
