import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TorusCong

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.St.G.FrameClose

theorem one_sub_T_zmod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  intro D X u
  obtain ⟨c', hc', hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) with hz'
  have hm' : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  have hzz : hA X.B.I z' z' = -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [hz', Formalism.L2.SG.PoincareInHH.Cut.hA_fmat, HidaSetting.zR, Formalism.L2.SG.PoincareInHH.Cut.hA_crd, X.zu_norm,
      map_neg, map_natCast, map_neg, map_natCast]
  set m : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) with hmdef
  set w0 : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 with hw0def
  have hw0 : w0 ∈ X.B.I.Lf := nat_smul_mem c' hz0
  have hw : m + w0 ∈ X.B.I.Lf := add_mem (mL_le X.B.g hm') hw0
  have h1 : ZMod' X.B.I X.B.g (hA X.B.I m (m + w0)) := zmod_of_mL hm' hw
  have h2 : ZMod' X.B.I X.B.g (hA X.B.I w0 m) := by
    rw [hA_symm]; exact Z_sig _ _ (zmod_of_mL hm' hw0)
  have hsplit : hA X.B.I (m + w0) (m + w0) - hA X.B.I w0 w0 = hA X.B.I m (m + w0) + hA X.B.I w0 m := by
    rw [hA_add_left, hA_add_right, hA_add_right]; ring
  have hmw : m + w0 = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    rw [hmdef, hw0def, ← smul_add, sub_add_cancel]
  have hsq : ∀ x : VA X.B.I, hA X.B.I ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x)
      = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * hA X.B.I x x := by
    intro x; rw [hA_nat_left, hA_smul_right]; ring
  have hA1 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0)) := by
    have e : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) =
        hA X.B.I m (m + w0) + hA X.B.I w0 m := by
      rw [← hsplit, hmw, hw0def, hsq, hsq]; ring
    rw [e]; exact Z_add _ _ h1 h2
  have hA2 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1)) := by
    have := Z_smul X.B.I X.B.g (natCast_mem (IntAf X.B.I.F X.B.I.E) (c' ^ 2)) X.formsAtZero.1
    simpa [Nat.cast_pow] using this
  refine ⟨c' ^ 2, Nat.Coprime.pow_left 2 hc', ?_⟩
  have e : ((c' ^ 2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) +
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1) := by
    rw [hzz, Nat.cast_pow]; ring
  rw [e]; exact Z_add _ _ hA1 hA2

end GlobalTheory.TorusCong
