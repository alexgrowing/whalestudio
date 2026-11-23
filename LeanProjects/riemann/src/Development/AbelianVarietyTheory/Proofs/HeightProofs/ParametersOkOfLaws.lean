import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfEXIffOriented
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelDvdBadN
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel

set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem liftIndexParameterConditions_of_coreAndShortLaws : ∀ (D : D7) (J : CoreJ D) (T : Top D) (EX : ErrX D) (p : ℕ), LawsJ J → LawsP T → LawsSh T → T.toCore = J.toCore → T.Q.Canon → FieldOK0 D p → HalfEX T.toCore EX → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1 ∧ (T.dδ j n).pd = p) → ∀ j, InR D j → ParOK T EX p j := by
  intro D J T EX p hJ hP hS hT hC hF hH hd j hj
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  have hpin : T.Q.Pins := hP.toLawsCore.pins
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hpin.2.1.1
  have hA : T.Q.l.A = 1 := hpin.2.1.2
  have hp : 0 < p := by
    rcases hF.own with e | e
    · exact e ▸ D.host.pde_prime.pos
    · exact e ▸ D.host.pde'_prime.pos
  refine ⟨hS, fun i hi n => (hd i hi n).1, key _ hT, (GlobalTheory.TrivLevel.badN_pos_iff D).2 hF.bad, fun n => (hd j hj n).2,
    (GlobalTheory.PtTie.halfEX_iff_oriented D T hP EX).1 hH, ?_⟩
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D T.Q hpin hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp) hF.curve j hj T.Q.l (T.Q.Xo j) T.Q.c hA ?_ rfl
  rw [hM]
  exact dvd_mul_right _ _

end GlobalTheory.FinalJoin2
