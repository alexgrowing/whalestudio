import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpacesNormHasFrame

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

theorem GlobalTheory.Mem.exists_diagSpaces_norm : ∀ (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T), ∃ S : Spaces R F E, S.T = T ∧ DiagSpaces S ∧ (∀ j, S.Vneg j = false) ∧ (∀ j, 0 < j → j < R.m → HasHyperbolicAuxiliaryFrame S j) ∧ (S.X R.m).hT S.z S.z = (S.T : E) ∧ ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j := by
  intro R F E _ _ _ _ _ _ cm T hT pz hpz
  exact ⟨DiagSp.spacesNorm R cm T hT pz hpz, DiagSp.spacesNorm_T R cm T hT pz hpz,
    DiagSp.spacesNorm_coord R cm T hT pz hpz, DiagSp.spacesNorm_Vneg R cm T hT pz hpz,
    fun j _ hj => DiagSp.spacesNorm_hasFrame R cm T hT pz hpz j hj,
    DiagSp.spacesNorm_z_norm R cm T hT pz hpz,
    fun j _ τ => DiagSp.spacesNorm_Y_sig R cm T hT pz hpz j τ⟩
