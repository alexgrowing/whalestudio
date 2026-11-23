import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PhiEmbed

theorem baseChange_injective₂ {D : D7} (p : PlF D) : Function.Injective (baseChange₂ D p) := by
  intro x y hxy
  refine (VS D).frame.ext_elem fun i => ?_
  have := congrFun hxy i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (D.s.atP p).ιE.injective this

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩⟩

set_option maxHeartbeats 1000000 in

theorem phi_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨hext, hUW, -, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  choose e he using fun (g : GV D) (p : PlF D) => (hext g p).exists
  have ext_one : ∀ p, Ext p (1 : GV D) (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := fun p x => rfl
  have ext_mul : ∀ p (a b : GV D) ga gb, Ext p a ga → Ext p b gb → Ext p (a * b) (ga * gb) := by
    intro p a b ga gb ha hb x
    show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
    rw [hb, ha]
  let φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0) :=
    { toFun := fun h p => ⟨e h p, hUW h h.2 p _ (he h p)⟩
      map_one' := by
        funext p
        apply Subtype.ext
        exact (hext 1 p).unique (he _ p) (ext_one p)
      map_mul' := by
        intro a b
        funext p
        apply Subtype.ext
        exact (hext _ p).unique (he _ p) (ext_mul p _ _ _ _ (he a p) (he b p)) }
  refine ⟨φ, ?_, fun h p => he h p⟩
  intro a b hab
  obtain ⟨p⟩ := exists_place D
  have h1 : e a p = e b p := congrArg Subtype.val (congrFun hab p)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply baseChange_injective₂ p
  rw [← he a p x, ← he b p x, h1]

end GlobalTheory.PhiEmbed
