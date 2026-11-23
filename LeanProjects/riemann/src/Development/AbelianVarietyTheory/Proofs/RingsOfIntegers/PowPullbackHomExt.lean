import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPowerStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PowOLinear

theorem pow_hom_ext {S : Scheme.{0}} {G' G Z : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {a b : Z ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  Fan.IsLimit.hom_ext p.lim a b h

theorem pow_pullback_hom_ext {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G']
    [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {Z : Over S'} {a b : Z ⟶ (Over.pullback f).obj G'}
    (h : ∀ i, a ≫ (Over.pullback f).map (p.pr i) = b ≫ (Over.pullback f).map (p.pr i)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) p.lim).hom_ext fun i => h i.as

theorem res_pullU_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}
    (g : Z ⟶ splitTorus S X) (χ : X) (h : ⊤ ≤ g.left ⁻¹ᵁ ⊤) :
    (res h (pullU g.left ⊤ (charUnit S X χ))).val = g.left.appTop.hom (charUnit S X χ).val := by
  have : (res h (pullU g.left ⊤ (charUnit S X χ))).val =
      (g.left.appLE ⊤ ⊤ h).hom (charUnit S X χ).val := rfl
  rw [this, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

theorem charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] :
    (charUnit S X 0).val = 1 := by
  have h := SplitTorusHom.charUnit_add (S := S) (0 : X) 0
  rw [add_zero] at h
  exact ((charUnit S X 0).isUnit.mul_eq_left.mp h.symm)

theorem torusEndOf_pow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {j : ℕ}
    (xe : X' ≃+ (Fin j → X)) (pr : Fin j → (splitTorus S X' ⟶ splitTorus S X))
    (hpr : ∀ (i : Fin j) (χ : X),
      res (fun x _ => show (pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
        (pullU (pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)))
    (h : X →+ X) (h' : X' →+ X') (hh : ∀ x i, xe (h' x) i = h (xe x i))
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t)
    (t' : splitTorus S X' ⟶ splitTorus S X') (htt : ∀ i, t' ≫ pr i = pr i ≫ t) :
    TorusEndOf X' h' t' := by
  have hpr' : ∀ i χ, (pr i).left.appTop.hom (charUnit S X χ).val =
      (charUnit S X' (xe.symm (Pi.single i χ))).val := fun i χ =>
    (res_pullU_val (pr i) χ _).symm.trans (congrArg Units.val (hpr i χ))
  have ht' : ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := fun χ =>
    (res_pullU_val t χ _).symm.trans (congrArg Units.val (ht χ))
  have key : ∀ y : Fin j → X, t'.left.appTop.hom (charUnit S X' (xe.symm y)).val =
      (charUnit S X' (h' (xe.symm y))).val := by
    intro y
    induction y using Pi.single_induction with
    | zero => rw [map_zero, map_zero, charUnit_zero, map_one]
    | add u v hu hv =>
      rw [map_add, map_add, SplitTorusHom.charUnit_add, SplitTorusHom.charUnit_add, map_mul, hu, hv]
    | single i χ =>
      have e : h' (xe.symm (Pi.single i χ)) = xe.symm (Pi.single i (h χ)) := by
        apply xe.injective
        funext k
        rw [hh, xe.apply_symm_apply, xe.apply_symm_apply]
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
      rw [e, ← hpr', ← hpr', ← SplitTorusHom.appTop_comp, htt, SplitTorusHom.appTop_comp, ht']
  intro x
  apply Units.ext
  refine (res_pullU_val t' x _).trans ?_
  have := key (xe x)
  rwa [xe.symm_apply_apply] at this

end PowOLinear

open PowOLinear in

theorem oLinear_of_unifPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x) → ∀ (ιD : D.OAct O) (ιD' : D'.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), (∀ a i, ιD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ ιD.onB.act a) → (∀ a i, ιA'.act a ≫ pA.pr i = pA.pr i ≫ ιA.act a) → (∀ a i, ιG'.act a ≫ pG.pr i = pG.pr i ≫ ιG.act a) → U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P O _ _ _ _ hxe ιD ιD' ιA ιA' ιG ιG'
    hD hA hG hU
  refine ⟨fun a => ?_, fun e a => ?_, fun e a => ?_⟩
  · refine pow_hom_ext pA.toIsPowGrp fun i => ?_
    rw [Category.assoc, Category.assoc, hA, P.gen_pr, ← Category.assoc U'.gen.hom, P.gen_pr,
      ← Functor.map_comp_assoc, hG, Functor.map_comp_assoc, hU.ext, Category.assoc]
  · refine pow_pullback_hom_ext (thick R I e) pD.pw fun i => ?_
    have h₁ := P.q_pr e i
    have h₂ := hU.q_lin e a
    have h₃ := congrArg (Over.pullback (thick R I e)).map (hD a i)
    have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
    rw [Functor.map_comp, Functor.map_comp] at h₃ h₄
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    rw [h₃, h₁, ← Category.assoc, h₄, Category.assoc, h₂, ← Category.assoc, ← h₁, Category.assoc]
  · obtain ⟨pT, hi, hc⟩ := GlobalTheory.T.productUniformization_torus_isPower R I j D D' A A' G G' pD pA pG U' U P e
    obtain ⟨t, ht, hti⟩ := hU.i_lin e a
    obtain ⟨t', ht'⟩ : ∃ t' : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X,
        ∀ i, t' ≫ pT.pr i = pT.pr i ≫ t :=
      ⟨Fan.IsLimit.lift pT.lim fun i => pT.pr i ≫ t, fun i => Fan.IsLimit.fac pT.lim _ i⟩
    refine ⟨t', ?_, ?_⟩
    · exact torusEndOf_pow pD.xe pT.pr hc (DistribSMul.toAddMonoidHom _ (star a))
        (DistribSMul.toAddMonoidHom _ (star a)) (fun x i => congrFun (hxe (star a) x) i) t ht t' ht'
    · refine pow_pullback_hom_ext (thick R I e) pG fun i => ?_
      have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
      rw [Functor.map_comp, Functor.map_comp] at h₄
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      rw [h₄, hi, ← Category.assoc, hi, Category.assoc, hti, ← Category.assoc, ← ht', Category.assoc]

end GlobalTheory
