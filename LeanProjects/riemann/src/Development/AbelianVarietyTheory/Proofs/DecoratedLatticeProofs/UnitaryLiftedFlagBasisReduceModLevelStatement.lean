import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLiftedFlagBasisReduceModLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  first | exact @GlobalTheory.FlagUnit.unitary_reduce | exact GlobalTheory.FlagUnit.unitary_reduce | (intros; apply GlobalTheory.FlagUnit.unitary_reduce <;> assumption)
