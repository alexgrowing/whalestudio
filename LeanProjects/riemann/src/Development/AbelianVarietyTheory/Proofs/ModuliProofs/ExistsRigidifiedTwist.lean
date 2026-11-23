import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.RigidifyTwist

open CechPic

theorem pull_cls_eq_zero {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (r : Z ⟶ X) (i : L.ι)
    (hi : ∀ z, r z ∈ L.U i) : CechPic.pull r (cls L hL) = 0 := by
  rw [← cls_pull hL r (pull_isLB hL r), cls_eq_zero_iff]
  refine (iso_triv_iff _).1 (iso_of_chart (pull_isLB hL r) ⟨fun _ _ => i, fun _ y _ => mem_pull.2 (hi y), ?_⟩)
  intro y p q hp hq
  rw [gm_pull_g L r (𝟙 Z) y (fun _ => i) (fun _ => i) (mem_pull.2 (hi y)) (mem_pull.2 (hi y))]
  have hy : (𝟙 Z ≫ r) y ∈ L.U i := by
    simpa using hi y
  rw [gm_self hL _ y hy]
  exact map_one _

theorem eSec_hom {S : Scheme.{0}} (A : Over S) [GrpObj A] : eSec A ≫ A.hom = 𝟙 S := by
  unfold eSec
  exact (Over.w _).trans rfl

private theorem cls_pull_tens_dual_eq_sub {S Y : Scheme.{0}} (A : Over S) (M : LB A.left) (hM : M.IsLB) (N : LB S)
    (hN : N.IsLB) (f : Y ⟶ A.left) (h : ((tens M (dual (N.pull A.hom))).pull f).IsLB) :
    cls _ h = pull f (cls M hM) - pull (f ≫ A.hom) (cls N hN) := by
  have hP := pull_isLB hN A.hom
  rw [cls_pull (isLB_tens hM (isLB_dual hP)) f h, cls_tens hM (isLB_dual hP), cls_dual hP,
    cls_pull hN A.hom, map_add, map_neg, pull_comp, sub_eq_add_neg]

private theorem pGen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) : PGen w := by
  intro Y f y j1 j2 k1 k2 h1 h2 h3 h4
  unfold gw
  have m1 : f y ∈ (L.pull F).U (fun _ => j1) := mem_pull.2 h1
  have m2 : f y ∈ (L.pull F).U (fun _ => j2) := mem_pull.2 h2
  have hV : f y ∈ ((L.pull F).div L').U (fun _ => j1, k1) ⊓ ((L.pull F).div L').U (fun _ => j2, k2) :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j1, k1) (fun _ => j2, k2))
  rw [map_mul, gm_res f y _ hV, gm_res f y _ hV, gm_div' (L.pull F) L' f y _ _ ⟨m1, h3⟩ ⟨m2, h4⟩,
    gm_pull_g L F f y _ _ m1 m2] at e
  exact e

private theorem lbIso_tens_dual_pull_eSec_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB)
    (U : S.Opens) (j : (M.pull (eSec A)).ι) (hU : U ≤ (M.pull (eSec A)).U j) :
    LBIso ((tens M (dual ((M.pull (eSec A)).pull A.hom))).pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hT := isLB_tens hM (isLB_dual (pull_isLB hN A.hom))
  have hz : ∀ z : U.toScheme, U.ι z ∈ (M.pull (eSec A)).U j := fun z => by
    exact hU z.2
  refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
  rw [cls_pull_tens_dual_eq_sub A M hM _ hN, ← morphismRestrict_ι, pull_comp, pull_cls_eq_zero hN U.ι j hz, map_zero,
    sub_zero, cls_pull hM]

theorem exists_rigidified_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left), M.IsLB → ∃ M' : LB A.left, M'.IsLB ∧ Out.Rigidified A M' ∧ (∀ p : S, ∃ U : S.Opens, p ∈ U ∧ LBIso (M'.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), φ ≫ A.hom = π ≫ x → LBIso (M'.pull φ) (M.pull φ)) ∧ (IsProper A.hom → Out.RelAmple A M → Out.RelAmple A M') := by
  intro S A _ M hM
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hP : ((M.pull (eSec A)).pull A.hom).IsLB := pull_isLB hN _
  have hT : (tens M (dual ((M.pull (eSec A)).pull A.hom))).IsLB := isLB_tens hM (isLB_dual hP)
  refine ⟨tens M (dual ((M.pull (eSec A)).pull A.hom)), hT, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hT _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, eSec_hom A, pull_id, cls_pull hM (eSec A) hN, sub_self]
  · intro p
    obtain ⟨j, hj⟩ := exists_chart hN p
    exact ⟨_, hj, lbIso_tens_dual_pull_eSec_restrict A M hM _ j le_rfl⟩
  · intro K _ x X φ π hφ
    obtain ⟨j, hj⟩ := exists_chart hN (x (Classical.arbitrary (Sp K)))
    have hx : ∀ z, x z ∈ (M.pull (eSec A)).U j := fun z => by
      rw [Subsingleton.elim z (Classical.arbitrary _)]
      exact hj
    refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, hφ, pull_comp, pull_cls_eq_zero hN x j hx, map_zero, sub_zero, cls_pull hM]
  · intro hpr hamp
    have := hpr
    refine AmpleLocal.relAmple_of_locally S A _ hT inferInstance inferInstance fun s => ?_
    obtain ⟨j, hj⟩ := exists_chart hN s
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hj
    obtain ⟨w, hw⟩ := lbIso_tens_dual_pull_eSec_restrict A M hM V j hVle
    have hpw : PGen w := pGen_of_isGen w hw
    exact ⟨V, hsV, relAmple_pull (A' := Over.mk (A.hom ∣_ V)) (isPullback_morphismRestrict A.hom V).flip hM
      (pull_isLB hT _) (w := w) hpw V hV (fun y => y.2) hamp⟩

end GlobalTheory.RigidifyTwist
