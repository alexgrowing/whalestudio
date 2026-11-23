import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorSquare
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogenyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincareDescent

theorem descend_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hP hadd hzero hi hq hfin hflat hsurj hsq hN
  haveI : IsFinite q.left := hfin
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_whisker (A := B) q
  haveI : IsFinite (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hfin
  haveI : Flat (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hflat
  haveI : Surjective (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hsurj
  haveI : IsLocallyNoetherian (A' ⊗ B).left := by
    haveI := hA'.smooth
    haveI := hB.smooth
    haveI : LocallyOfFiniteType (A' ⊗ B).hom := by
      show LocallyOfFiniteType (pullback.fst A'.hom B.hom ≫ A'.hom)
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (A' ⊗ B).hom
  have hker : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B)) := by
    intro T x hx
    have e : (1 : T ⟶ A) ≫ q = x ≫ q := by rw [hx, MonObj.one_comp]
    have hx' : x = (hsq.lift 1 x e ≫ snd A N) ≫ i := by
      have h2 := hsq.lift_snd 1 x e
      rw [MonObj.comp_mul, hsq.lift_fst, _root_.one_mul, ← Category.assoc] at h2
      exact h2.symm
    obtain ⟨n, rfl⟩ : ∃ n : T ⟶ N, x = n ≫ i := ⟨_, hx'⟩
    rw [triv_ev_iff hP]
    have z := congrArg (CechPic.pull (lift (fst T B ≫ n) (snd T B)).left) ((triv_ev_iff hP _ _).1 hN)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd, Category.assoc] at z
    exact z
  obtain ⟨φ, hc, hco⟩ := GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny K A A' B q P hA hA' hB hq hfin hflat hsurj hP hadd hzero hker
  obtain ⟨P₀, hP₀, hiso⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ (q ▷ B).left P hP φ hc hco
  refine ⟨P₀, hP₀, (cls_eq_iff (pull_isLB hP₀ _) hP).1 ?_⟩
  refine Eq.trans ?_ ((cls_eq_iff hP (pull_isLB hP₀ _)).2 hiso).symm
  rw [cls_ev hP₀, evc, cls_pull hP₀, ← lift_whiskerRight, lift_fst_snd, Category.id_comp]

end GlobalTheory.PoincareDescent
