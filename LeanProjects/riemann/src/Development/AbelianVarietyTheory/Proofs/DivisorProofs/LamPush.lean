import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorSym

open GlobalTheory.CechPic GlobalTheory.EndRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def genι (G : Over (Sp R)) : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

theorem lam_push (U : UnifPre I D A G) {T : Over (Sp (FractionRing R))} (x y : T ⟶ (Over.pullback (jK R)).obj G) :
    @id (Pic T.left) (lam (T := (Over.map (jK R)).obj T) (cls _ U.LG.isLB) (push (genι G) x) (push (genι G) y)) =
      lam (cls _ A.isLB) (x ≫ U.gen.hom) (y ≫ U.gen.hom) := by
  have := U.gen_hom
  have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
  rw [cls_pull A.isLB, cls_pull U.LG.isLB] at e
  have hm : ∀ x y : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) (x * y) = push (genι G) x * push (genι G) y :=
    fun x y => push_mul (genι G) (𝟙 _) (Category.id_comp _).symm x y
  have h1 : push (genι G) (1 : T ⟶ (Over.pullback (jK R)).obj G) = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hp : ∀ x : T ⟶ (Over.pullback (jK R)).obj G,
      @id (Pic T.left) (pull (push (genι G) x).left (cls _ U.LG.isLB)) =
        pull x.left (pull U.gen.hom.left (cls _ A.isLB)) := fun x => by
    rw [e, ← pull_comp]; rfl
  rw [← lam_pull U.gen.hom, lam, lam, ← hm, ← h1, ← hp, ← hp, ← hp, ← hp]
  rfl

theorem lam_act (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.OAct O}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) {T : Over (Sp (FractionRing R))}
    (x y : (Over.map (jK R)).obj T ⟶ G) :
    lam (cls _ U.LG.isLB) (x ≫ oG.act a) y = lam (cls _ U.LG.isLB) x (y ≫ oG.act (star a)) := by
  have sj : ∀ x : (Over.map (jK R)).obj T ⟶ G, ∃ x' : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) x' = x :=
    fun x => ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨x, rfl⟩ := sj x
  obtain ⟨y, rfl⟩ := sj y
  have e' : ∀ f : G ⟶ G, push (genι G) ((Over.pullback (jK R)).map f) = genι G ≫ f := fun f =>
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  rw [← push_comp _ (e' _), ← push_comp _ (e' _)]
  refine (lam_push U _ _).trans (Eq.trans ?_ (lam_push U _ _).symm)
  obtain ⟨t, ht⟩ := GlobalTheory.RosatiDescent.exists_gen_of_rosatiAdj (oA.rosati a)
  have := cls_of_rosati A.isLB t ht (x ≫ U.gen.hom) (y ≫ U.gen.hom)
  rw [Category.assoc, Category.assoc, h.ext, h.ext, ← Category.assoc, ← Category.assoc, lam, lam, this]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F hF A' G' _ _ _ U' oA oG hlin G _ _ _ inc pr _ _ hip hpi κ₀ hκ
  have hs : oG.act (star F.e * F.f * F.e) = oG.act (star F.e * star F.f * F.e) :=
    congrArg oG.act hF.2.1
  have hi : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  let GK := (Over.pullback (jK R)).obj G
  have hL := U'.LG.isLB
  have sy : ∀ x y : (Over.map (jK R)).obj (G2 GK) ⟶ G,
      lam (cls _ hL) (x ≫ inc) (y ≫ inc ≫ oG.act F.f) = lam (cls _ hL) (y ≫ inc) (x ≫ inc ≫ oG.act F.f) := fun x y => by
    have e₁ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act F.f)
    have e₂ := lam_act U'.toUnifPre hlin F.f (x ≫ inc) (y ≫ inc)
    have e₃ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act (star F.f))
    have e₄ : inc ≫ oG.act F.f ≫ oG.act (star F.e) = inc ≫ oG.act (star F.f) ≫ oG.act (star F.e) := by
      have := congrArg (inc ≫ ·) hs
      simpa only [oG.map_mul, reassoc_of% hi] using this
    simp only [Category.assoc, hi] at e₁ e₂ e₃
    rw [e₁, e₄, ← e₃, ← e₂, lam_comm]
  have hP := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hL)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  refine (gen_iff_sum (pull_isLB hP κ₀) _ _).2 ?_
  rw [cls_pull hP, GlobalTheory.FullSiegel.cls_lam_pull hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← pull_comp]
  let X : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (fst GK GK)
  let Y : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (snd GK GK)
  have k₁ : κ₀ = (lift X Y).left := by
    refine pullback.hom_ext (hκ.1.trans ?_) (hκ.2.trans ?_)
    · exact (congrArg (·.left) (lift_fst X Y)).symm
    · exact (congrArg (·.left) (lift_snd X Y)).symm
  have k₂ : (lift (snd GK GK) (fst GK GK)).left ≫ κ₀ = (lift Y X).left := by
    rw [k₁]; exact lift_push (genι G) _ _
  have p₁ := pull_lam (lift X Y) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  have p₂ := pull_lam (lift Y X) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  rw [lift_fst_assoc, lift_snd_assoc] at p₁ p₂
  rw [← k₁] at p₁
  rw [← k₂] at p₂
  exact add_neg_eq_zero.2 (p₂.trans ((sy Y X).trans p₁.symm))

end GlobalTheory.Mum.FactorSym
