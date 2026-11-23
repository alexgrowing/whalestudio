import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.DiagPull

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

def pairCls (X : Obj F 𝔠 S) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) : GlobalTheory.CechPic.Pic T.left :=
  GlobalTheory.CechPic.pull (lift u v).left (cls (X.P c) (X.isLB c))

theorem pairCls_comp (X : Obj F 𝔠 S) (c : 𝔠.elt) {T T' : Over S} (g : T' ⟶ T) (u v : T ⟶ X.A) :
    GlobalTheory.CechPic.pull g.left (pairCls X c u v) = pairCls X c (g ≫ u) (g ≫ v) := by
  unfold pairCls
  rw [← comp_lift, Over.comp_left]
  exact (GlobalTheory.CechPic.pull_comp _ _ _).symm

theorem pairCls_symm (X : Obj F 𝔠 S) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) :
    pairCls X c u v = pairCls X c v u := by
  have h : cls (X.P c) (X.isLB c) = pairCls X c (snd X.A X.A) (fst X.A X.A) :=
    (cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) _)).2 (X.symm c)
  have h2 := pairCls_comp X c (lift u v) (snd X.A X.A) (fst X.A X.A)
  rw [lift_fst, lift_snd] at h2
  exact (congrArg (GlobalTheory.CechPic.pull (lift u v).left) h).trans h2

theorem pairCls_smul (X : Obj F 𝔠 S) (a : 𝓞 F) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) :
    pairCls X (a • c) u v = pairCls X c u (v ≫ X.rm.act a) := by
  have h : cls (X.P (a • c)) (X.isLB _) = pairCls X c (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) :=
    (cls_eq_iff (X.isLB _) (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  have h2 := pairCls_comp X c (lift u v) (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a)
  rw [lift_fst, lift_snd_assoc] at h2
  exact (congrArg (GlobalTheory.CechPic.pull (lift u v).left) h).trans h2

theorem pull_act_cls_diag {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S)
    (b : 𝓞 F) (c : 𝔠.elt) :
    GlobalTheory.CechPic.pull (X.rm.act b).left (cls (X.diag c) (pull_isLB (X.isLB c) _)) =
      cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) := by
  change GlobalTheory.CechPic.pull (X.rm.act b).left (pairCls X c (𝟙 _) (𝟙 _)) = pairCls X ((b * b) • c) (𝟙 _) (𝟙 _)
  rw [pairCls_comp, mul_smul, pairCls_smul, pairCls_symm X (b • c), pairCls_smul, Category.comp_id,
    Category.id_comp]

end GlobalTheory.RealMult.DiagPull
