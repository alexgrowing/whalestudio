import Development.EtaleCohomology.EtaleTrace.LCycleCut
import Development.EtaleCohomology.TateTwists.MayerVietorisExactSequence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LDblPf

def LMvWeak : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  (∀ (n : ℤ) (a : H R U F n) (b : H R V F n), pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b →
    ∃ x : H R E F n, pull R f F n x = a ∧ pull R g F n x = b) ∧
  ∀ m : ℤ, (∀ c : H R (pullback f g) F m, ∃ a b, c = pull R (pullback.fst f g) F m a - pull R (pullback.snd f g) F m b) →
    ∀ x : H R E F (m + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

instance monoSch {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map U.ι).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

instance freePres (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1} R)) := (ModuleCat.adj _).leftAdjoint_preservesColimits
  unfold free freeP
  infer_instance

def LDblCover : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (U : X.Opens),
  Cover2 R (LCycleCut.i1 U) (LCycleCut.i2 U) ∧
    IsPullback (sch.map U.ι) (sch.map U.ι) (LCycleCut.i1 U) (LCycleCut.i2 U)

end LateralTheory.EtaleTrace.LDblPf
