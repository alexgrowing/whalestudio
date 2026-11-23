import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_complement_frame_diag_mod_conductor : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  first | exact @GlobalTheory.ScalW.scalar_diag_mod_g | exact GlobalTheory.ScalW.scalar_diag_mod_g | (intros; apply GlobalTheory.ScalW.scalar_diag_mod_g <;> assumption)
