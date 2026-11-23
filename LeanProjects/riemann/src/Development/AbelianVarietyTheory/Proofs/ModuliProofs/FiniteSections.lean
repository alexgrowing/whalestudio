import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.AmpleStabTorsion

theorem finite_sections {k : Type} [Field k] [IsAlgClosed k] (H : Over (Sp k)) [IsFinite H.hom] :
    Finite (Out.baseOver (Sp k) ⟶ H) := by
  have hfin : (Set.univ : Set H.left).Finite :=
    (H.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  have : Finite H.left := Set.finite_univ_iff.1 hfin
  refine Finite.of_injective
    (fun y : Out.baseOver (Sp k) ⟶ H => (y.left : Sp k ⟶ H.left) (IsLocalRing.closedPoint k)) fun y y' h => ?_
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.hom (Over.w y) (Over.w y') h)

theorem exists_pow_eq_one : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ x : Out.baseOver (Sp k) ⟶ A, Triv (Out.translDiff A M x) → ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  intro hL k _ _ A _ _ hA M hM hamp x hx
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy k A M hM).1 hamp
  obtain ⟨h0, -, htw⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns k A hA ⟨_, isLB_pw hM d, n, s, hs⟩ M _ hM h0
  have := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns k A hA M _ hM h0 hamp H j hj hH
  have := finite_sections H
  have hxK : x ∈ GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) := by
    obtain ⟨c, hc⟩ := hx
    exact fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  have hfin : ((GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) : Set (Out.baseOver (Sp k) ⟶ A))).Finite :=
    (Set.finite_range fun y : Out.baseOver (Sp k) ⟶ H => y ≫ j).subset fun z hz =>
      (hH _ z).1 ((htw _ rfl _ z).1 hz)
  have : Finite (GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k))) := hfin
  obtain ⟨m, hm, e⟩ := (isOfFinOrder_of_finite (⟨x, hxK⟩ : GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)))).exists_pow_eq_one
  exact ⟨m, hm, congrArg Subtype.val e⟩

end GlobalTheory.AmpleStabTorsion
