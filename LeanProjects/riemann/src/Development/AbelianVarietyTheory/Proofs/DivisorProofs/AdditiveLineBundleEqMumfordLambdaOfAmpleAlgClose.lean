import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AddLineField

open GlobalTheory.PrimitiveOverField in

theorem additive_eq_lam_of_ample : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  intro K _ _ A _ hA L hL hamp N hN
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have hpr : IsProjBy A.hom := by
    obtain ⟨_, _, m, s, hH, hv⟩ := veryAmpleBy_of_relAmple hL hamp (𝟙 A.left) (Category.id_comp _)
      (pull_isLB hL (𝟙 A.left)) (GlobalTheory.lbIso_self (pull_isLB hL _))
    exact ⟨_, hH, m, s, hv⟩
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f A.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.exists_gen_theta_of_isProjBy K A hA hpr L hL
  obtain ⟨S, hS, hSK⟩ := GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed K A hA L hL hamp
  let O : LB A.left := ev N (𝟙 A) (toUnit A)
  have hO : O.IsLB := pull_isLB hN.isLB _
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have pO : ∀ {Y : Over (Sp K)} (u : Y ⟶ A), CechPic.pull u.left (cls O hO) = evc hN.isLB u (toUnit Y) := by
    intro Y u
    rw [cls_ev hN.isLB, pull_evc, Category.comp_id, comp_toUnit]
  have lamO : lam (cls O hO) (fst A A) (snd A A) = 0 := by
    have e := (isAdditive_iff hN.isLB).1 hN.add (A ⊗ A) (fst A A) (snd A A) (toUnit _)
    have e1 := hN.add.evc_one hN.isLB (toUnit (A ⊗ A))
    simp only [lam, pO, e, e1]
    abel
  have key : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO = lam (cls L hL) (toUnit A ≫ x) (𝟙 A) →
      Same A N (abelian₂ A L) (𝟙 _) x := by
    intro x hx
    rw [same_iff hN.isLB hLam]
    have e1 : evc hN.isLB (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ 𝟙 _) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (cls O hO) := by
      rw [pO, Category.comp_id, toUnit_unique (toUnit _) (snd A _)]
    have e2 : evc hLam (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ x) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (lam (cls L hL) (toUnit A ≫ x) (𝟙 A)) := by
      have cL : cls (abelian₂ A L) hLam = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hLam
      rw [evc, cL, pull_lam, pull_lam, lift_fst,
        lift_snd, Category.comp_id, ← Category.assoc, toUnit_unique (fst A _ ≫ toUnit A) (snd A _), lam_comm]
    rw [e1, e2, hx]
  by_contra hno
  have hno' : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO ≠ lam (cls L hL) (toUnit A ≫ x) (𝟙 A) :=
    fun x e => hno ⟨x, key x e⟩
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst A A) (snd A A) - CechPic.pull (snd A A).left (cls O hO))
  have hpq : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ A, (toUnit A ≫ x).left = A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (toUnit A ≫ x) (𝟙 A)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (𝟙 A) (toUnit A ≫ x)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst A A).left ≫ A.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
    refine ⟨(lift (toUnit A ≫ x') (𝟙 A)).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit A ≫ x') (𝟙 A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit A ≫ x') (𝟙 A))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno' x' e.symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ A.left := η[A].left
  have ho : o ≫ A.hom = 𝟙 _ := Over.w η[A]
  have all := GlobalTheory.T.lineBundle_product_acyclic_over_affine_finite_closed K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance
    inferInstance F hF S hS (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
      refine ⟨(lift (𝟙 A) (toUnit A ≫ x')).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have hm := hSK x' e
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (by rw [hy]; exact hm)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 A) (toUnit A ≫ η[A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (cst_left η[A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ η[A])))
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : Nonempty A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.AddLineField
