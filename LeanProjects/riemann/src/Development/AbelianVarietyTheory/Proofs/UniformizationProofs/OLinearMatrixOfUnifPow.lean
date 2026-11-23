import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusProj

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

theorem row_comm {M N M' N' : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
    {j : ℕ} (p : Fin j → (M' ⟶ M)) (r : Fin j → (N' ⟶ N)) (q : M ⟶ N) (hq : IsMonHom q)
    (q' : M' ⟶ N') (hpr : ∀ l, q' ≫ r l = p l ≫ q) (a : Fin j → (M ⟶ M)) (b : Fin j → (N ⟶ N))
    (hab : ∀ l, a l ≫ q = q ≫ b l) (m : M' ⟶ M') (n : N' ⟶ N') (i : Fin j)
    (hm : m ≫ p i = ∏ l, p l ≫ a l) (hn : n ≫ r i = ∏ l, r l ≫ b l) :
    (m ≫ q') ≫ r i = (q' ≫ n) ≫ r i := by
  rw [Category.assoc, Category.assoc, hpr, hn, ← Category.assoc, hm, prod_comp, comp_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Category.assoc, hab, ← Category.assoc, ← hpr, Category.assoc]

end General

theorem pullback_row {S S' : Scheme.{0}} (f : S' ⟶ S) {G G' : Over S} [GrpObj G] [IsCommMonObj G]
    {j : ℕ} (p : Fin j → (G' ⟶ G)) (a : Fin j → (G ⟶ G)) (m : G' ⟶ G') (i : Fin j)
    (h : m ≫ p i = ∏ l, p l ≫ a l) :
    (Over.pullback f).map m ≫ (Over.pullback f).map (p i) =
      ∏ l, (Over.pullback f).map (p l) ≫ (Over.pullback f).map (a l) := by
  rw [← Functor.map_comp, h]
  refine (map_prod ((Over.pullback f).homMonoidHom (X := G') (M := G)) _ _).trans ?_
  exact Finset.prod_congr rfl fun l _ => (Over.pullback f).map_comp (p l) (a l)

theorem pullback_hom_ext {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G']
    [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {Z : Over S'} {a b : Z ⟶ (Over.pullback f).obj G'}
    (h : ∀ i, a ≫ (Over.pullback f).map (p.pr i) = b ≫ (Over.pullback f).map (p.pr i)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) p.lim).hom_ext fun i => h i.as

theorem torusEndOf_iff {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem appTop_comp {S : Scheme.{0}} {A B C : Over S} (a : A ⟶ B) (b : B ⟶ C)
    (r : Γ(C.left, ⊤)) :
    (a ≫ b).left.appTop.hom r = a.left.appTop.hom (b.left.appTop.hom r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

theorem exists_torus_matrix {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {j : ℕ} (xe : X' ≃+ (Fin j → X)) (pr : Fin j → (splitTorus S X' ⟶ splitTorus S X))
    (hpr : ∀ (i : Fin j) (χ : X), (pr i).left.appTop.hom (charUnit S X χ).val =
      (charUnit S X' (xe.symm (Pi.single i χ))).val)
    (h : Fin j → Fin j → X → X) (h' : X' →+ X')
    (hh : ∀ s χ l, xe (h' (xe.symm (Pi.single s χ))) l = h s l χ)
    (t : Fin j → Fin j → (splitTorus S X ⟶ splitTorus S X))
    (ht : ∀ s l, TorusEndOf X (h s l) (t s l)) :
    ∃ t' : splitTorus S X' ⟶ splitTorus S X', TorusEndOf X' h' t' ∧
      ∀ s, t' ≫ pr s = ∏ l, pr l ≫ t s l := by
  let E' := splitTorusPointsEquiv S X' (splitTorus S X')
  let E := splitTorusPointsEquiv S X (splitTorus S X')
  have hu : ∀ x, (E' (𝟙 _) (Multiplicative.ofAdd x)).val = (charUnit S X' x).val := fun x => by
    rw [splitTorusPointsEquiv_val]
    simp
  obtain ⟨t', ht'⟩ := E'.surjective ((E' (𝟙 _)).comp (AddMonoidHom.toMultiplicative h'))
  have key : ∀ x, t'.left.appTop.hom (charUnit S X' x).val = (charUnit S X' (h' x)).val := by
    intro x
    rw [← splitTorusPointsEquiv_val, ← hu]
    exact congrArg (fun φ => (φ (Multiplicative.ofAdd x)).val) ht'
  refine ⟨t', (torusEndOf_iff _ _).2 key, fun s => E.injective ?_⟩
  rw [map_prod]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have e : h' (xe.symm (Pi.single s χ)) = ∑ l, xe.symm (Pi.single l (h s l χ)) := by
    apply xe.injective
    rw [← map_sum, xe.apply_symm_apply, Finset.univ_sum_single]
    funext l
    exact hh s χ l
  rw [MonoidHom.finset_prod_apply, Units.coe_prod, splitTorusPointsEquiv_val, appTop_comp, hpr, key,
    e, ← hu, ofAdd_sum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [hu, splitTorusPointsEquiv_val, appTop_comp, (torusEndOf_iff _ _).1 (ht s l), hpr]

end PowMatrixLinear

attribute [local instance] PowMatrixLinear.splitTorus_isCommMonObj in
open PowMatrixLinear in

theorem oLinear_matrix_of_unifPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (_ : UnifPowOf2 pD pA pG U' U) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module (Matrix (Fin j) (Fin j) O) D'.toPre.X] (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) (ιD' : D'.OAct (Matrix (Fin j) (Fin j) O)) (ιA' : A'.OAct (Matrix (Fin j) (Fin j) O)) (ιG' : RingAct G' (Matrix (Fin j) (Fin j) O)), U.OLinear O ιD ιA ιG → (∀ (m : (Matrix (Fin j) (Fin j) O)) (x : D'.toPre.X) (i : Fin j), pD.xe (m • x) i = ∑ l, m i l • pD.xe x l) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιD'.onB.act m ≫ pD.pw.pr i = ∏ l, pD.pw.pr l ≫ ιD.onB.act (m i l)) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιA'.act m ≫ pA.pr i = ∏ l, pA.pr l ≫ ιA.act (m i l)) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιG'.act m ≫ pG.pr i = ∏ l, pG.pr l ≫ ιG.act (m i l)) → U'.OLinear (Matrix (Fin j) (Fin j) O) ιD' ιA' ιG' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P O _ _ _ _ ιD ιA ιG ιD' ιA' ιG'
    hU hxe hD hA hG
  refine ⟨fun m => ?_, fun e m => ?_, fun e m => ?_⟩
  · refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    exact row_comm _ pA.pr U.gen.hom U.gen_hom U'.gen.hom P.gen_pr _ _ (fun l => hU.ext (m i l))
      _ _ i (pullback_row _ _ _ _ i (hG m i)) (hA m i)
  · refine pullback_hom_ext (thick R I e) pD.pw fun i => ?_
    exact row_comm _ _ (U.gt e).q (U.gt e).q_hom (U'.gt e).q (P.q_pr e) _ _
      (fun l => hU.q_lin e (m i l)) _ _ i (pullback_row _ _ _ _ i (hG m i))
      (pullback_row _ _ _ _ i (hD m i))
  · choose pr hi hc using GlobalTheory.PowTorusProj.exists_torus_proj R I j D D' A A' G G' pD pA pG U' U P e
    choose t ht hti using hU.i_lin e
    obtain ⟨t', h₁, h₂⟩ := exists_torus_matrix pD.xe pr hc (fun s l χ => star (m s l) • χ)
      (DistribSMul.toAddMonoidHom _ (star m)) (fun s χ l => by
        change pD.xe (star m • _) l = _
        rw [hxe, pD.xe.apply_symm_apply, Finset.sum_eq_single s]
        · rw [Pi.single_eq_same, Matrix.star_apply]
        · intro k _ hk
          rw [Pi.single_eq_of_ne hk, smul_zero]
        · intro h
          exact absurd (Finset.mem_univ s) h)
      (fun s l => t (m s l)) (fun s l => ht (m s l))
    refine ⟨t', h₁, pullback_hom_ext (thick R I e) pG fun s => ?_⟩
    exact (row_comm pr _ (U.gt e).i (U.gt e).i_hom (U'.gt e).i hi _ _
      (fun l => (hti (m s l)).symm) _ _ s (h₂ s) (pullback_row _ _ _ _ s (hG m s))).symm

end GlobalTheory
