import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFinsetContainsRayField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Plug.RayLarge

open Formalism.L2.Host

def raySet (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : Finset ℂ :=
  if h : M ≠ 0 then Classical.choose (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h) else ∅

theorem raySet_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : ∀ z ∈ raySet hR P M, IsAlgebraic ℚ z := by
  unfold raySet
  split_ifs with h
  · exact (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h)).1
  · simp

def levels (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℕ :=
  Classical.choose (GlobalTheory.Plug.TwistLevels.levels_bounded P f Ξ)

def raySets (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  (levels P f Ξ).biUnion (raySet hR P)

theorem raySets_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ raySets hR P f Ξ, IsAlgebraic ℚ z := by
  intro z hz
  obtain ⟨M, -, hz⟩ := Finset.mem_biUnion.1 hz
  exact raySet_alg hR P M z hz

theorem rayRec_of_has (hR : GlobalTheory.NT.RayField) {K : Ctx} (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T)
    (hH : ∀ z ∈ raySets hR X.B.toPre f (T.set f), ∃ x : X.B.LL, X.B.embLL x = z) : RayRec X.toD7 c.O.nch := by
  intro w Sp hSp
  have hspec := Classical.choose_spec (GlobalTheory.Plug.TwistLevels.levels_bounded X.B.toPre f (T.set f))
  have hM : X.B.host.g 0 * X.B.host.g 1 * ∏ q ∈ Sp.image (fun Q => Nat.card (kP Q)), q ∈ levels X.B.toPre f (T.set f) := by
    refine hspec.2 X.B rfl T HEq.rfl w Sp ?_
    intro P hP
    rcases hSp P hP with ⟨h1, -⟩ | ⟨hmu, hmem⟩
    · exact Or.inl h1
    · right
      have hw : w ∈ c.Wt := by_contra fun h => hmu (c.mu.off w h)
      rw [← (c.nch_Q w hw).1]
      exact hmem
  have hM0 := hspec.1 _ hM
  have hrs := (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR X.B.toPre _ hM0)).2
  refine hrs X.B.LL X.B.embLL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK X.toD7) ?_ ?_
  · ext x
    exact DFunLike.congr_fun X.B.embE_φ₀ _
  · intro z hz
    refine hH z (Finset.mem_biUnion.2 ⟨_, hM, ?_⟩)
    rw [raySet, dif_pos hM0]
    exact hz

end GlobalTheory.Plug.RayLarge

open GlobalTheory.Plug.RayLarge in

theorem GlobalTheory.Plug.largeBaseProperty_rayProperty : GlobalTheory.NT.RayField → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q : V4.Slot), LargeBaseCondition KP Q RayPosition := by
  intro hR KP Q
  exact ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B f _ _ Ξ => raySets hR B f Ξ, by simp,
      fun B f _ _ Ξ => raySets_alg hR B f Ξ,
      fun B f T _ hH _ _ _ C W V S N G c _ => rayRec_of_has hR ⟨B, C, W, V, S, N, G⟩ f T c fun z hz => hH.2 z hz⟩⟩⟩⟩⟩⟩

end
