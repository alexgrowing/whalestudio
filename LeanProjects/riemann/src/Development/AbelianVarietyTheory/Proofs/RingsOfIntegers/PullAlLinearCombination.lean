import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  unfold aF
  rw [lift_fst]

theorem gen_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have hβ : Function.Surjective (β_ (TF (R := V) F) D.toPre.P.A).hom.left.appTop.hom := by
    intro x
    refine ⟨(β_ (TF (R := V) F) D.toPre.P.A).inv.left.appTop.hom x, ?_⟩
    have hid : (β_ (TF (R := V) F) D.toPre.P.A).hom.left ≫ (β_ (TF (R := V) F) D.toPre.P.A).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hx := congrArg (fun g => g.appTop.hom x) hid
    first
      | simpa [Scheme.Hom.appTop] using hx
      | (simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at hx; exact hx)
  have hp : Function.Surjective (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom := by
    have h1 := surj_comp hβ (surj_snd hG D.toPre.P.isAb (TF (R := V) F))
    rwa [← Over.comp_left, braiding_hom_snd] at h1
  have he : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    unfold DegPre.zF
    rw [lift_fst, Over.id_left]
  refine gen_unique D.toPre.P.isLB _ _ he hp hu hu' ?_ Z r z J hJ
  intro y J' hJ'
  have e1 := val_pull hJ' u (DegPre.zF D.toPre F).left (𝟙 _)
  have e2 := val_pull hJ' u' (DegPre.zF D.toPre F).left (𝟙 _)
  rw [Category.id_comp] at e1 e2
  rw [← e1, ← e2, val_corr hJ' c, val_corr hJ' c']

private lemma sval_add_of_good {k : ℕ} (s s' : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((s + s').s α) r z J = sval (s.s α) r z J + sval (s'.s α) r z J := by
  unfold sval
  exact (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α _)).trans (gs_add _ _ _ (hJ.mem _ r) _ _)

theorem pull_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    obtain ⟨u', hu', hc', hr'⟩ := h1' χ
    refine ⟨u, hu, hc, ?_⟩
    refine (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    have e2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 hr' _ (𝟙 _) y J hJ
    have e3 := gen_val hG oa a k N χ hu' hu hc' hc _ (𝟙 _) y J hJ
    rw [sval_add_of_good _ _ _ _ _ hJ, sval_add_of_good _ _ _ _ _ hJ, e1, e2, e3, add_mul]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.add_f, h2 β hβ j, h2' β hβ j, add_zero]

private lemma sval_smul_eq_gs_gF_mul_of_good {k : ℕ} (ζ : F) (s : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((ζ • s).s α) r z J = gs r z ⊤ (gF D.toPre F ζ) * sval (s.s α) r z J := by
  unfold sval
  refine (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.smul_f ζ s α _)).trans ?_
  refine (gs_mul _ _ _ (hJ.mem _ r) _ _).trans ?_
  congr 1
  exact gs_res r z le_top (hJ.mem _ r) _

private lemma gs_aF_gF_eq_gs_gF (oa : D.toPre.OAct O) (a : O) (ζ : F) (y : (DegPre.BF D.toPre F).left) :
    gs (𝟙 _ ≫ (aF D F oa a).left) y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  have k1 : ∀ f : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left,
      gs f y ⊤ (gF D.toPre F ζ) = gs (f ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun f => gs_pull f _ y ⊤ (by simp) _
  rw [k1, k1, Category.assoc, aF_fst]

theorem pull_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    refine ⟨u, hu, hc, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_⟩
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    rw [sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, e1, gs_aF_gF_eq_gs_gF, _root_.mul_assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.smul_f, h2 β hβ j, mul_zero]

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N n : ℕ), 0 < n → ∀ (c : Fin n → F) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D.toPre F (k * N)), (∀ l, PullAl D F oa a k N (s l) (s' l)) → PullAl D F oa a k N (∑ l, c l • s l) (∑ l, c l • s' l) := by
  intro hG V _ _ _ D F _ _ O _ _ _ oa a k N n hn c s s' hs
  have key : ∀ S : Finset (Fin n), S.Nonempty →
      PullAl D F oa a k N (∑ l ∈ S, c l • s l) (∑ l ∈ S, c l • s' l) := by
    intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton l =>
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact pull_smul oa a k N (c l) (hs l)
    | cons l S hl hS ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact pull_add hG oa a k N (pull_smul oa a k N (c l) (hs l)) ih
  exact key Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩

end GlobalTheory.PullComb
