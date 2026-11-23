import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.NuBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Generic

variable {X Y Y' Z : Scheme.{0}}

theorem lin_of_sval {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J)
    (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  unfold resTop
  dsimp only
  refine fn_ext fun y hy0 => ?_
  have hy : (𝟙 Y) y ∈ LB.wchart L φ j := hy0
  show gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) = gs (𝟙 Y) y (LB.wchart L φ j) _
  obtain ⟨J, hJ, hs⟩ := sval_trans hL s y j hy
  have hy' := hJ.mem φ (𝟙 Y)
  have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ j) ((t i).f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval (t i) (𝟙 Y) y J := fun i =>
    (sec_trans (t i) (𝟙 Y) y hy hy').trans (congrArg _ (sval_of (t i) (𝟙 Y) y J _ fun _ => rfl).symm)
  rw [hs, H y J hJ, Finset.mul_sum, gs_fsum _ _ _ hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (gs_mul (𝟙 Y) y (LB.wchart L φ j) hy _ ((t i).f j)).symm
  rw [gs_res (𝟙 Y) y le_top hy (b i), e i]
  ring

theorem gs_one (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq r z ⊤ trivial, map_one, map_one]

end Generic

theorem le_val_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {T : Type} (S : Finset T)
    (a : T → F) (q : T → ℚ) (h : ∀ i, ((q i : ℚ) : WithTop ℚ) ≤ v (a i)) :
    ((∑ i ∈ S, q i : ℚ) : WithTop ℚ) ≤ v (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, v.map_mul, WithTop.coe_add]
    exact add_le_add (h x) ih

set_option maxHeartbeats 1600000 in

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ) (Fs : Fin j → Fam D.toPre F k) (F' : Fam D'.toPre F k), IsBoxFam pD F k F' Fs → ∀ r : Fin j → ℚ, (∀ i, NuGe D Q F v k (Fs i) (r i)) → NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k F' (∑ i, r i) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ v k Fs F' hB r hr
  unfold IsBoxFam at hB
  unfold NuGe at hr ⊢
  intro α'
  have hBα := hB α'
  clear hB
  obtain ⟨hφ, hB⟩ := hBα
  unfold VGe at hr ⊢
  choose n a σ σF hsc hv he using fun i => hr i (pD.xe α' i)
  clear hr
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB

  choose σB hσB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφB α') (DegPre.famε k)
      (fun i => (pD.pw.pr i).left) (fun i => D.toPre.famφB (pD.xe α' i)) (famφB_pr pD α')
      (fun i => σ i (m i))

  choose σFB hσFB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφ F α') (DegPre.famε k)
      (prB pD F) (fun i => D.toPre.famφ F (pD.xe α' i)) hφ (fun i => σF i (m i))
  have hpr : ∀ i, (DegPre.prB D'.toPre F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D.toPre F).left := by
    intro i
    unfold prB
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold DegPre.prB
    simp
  have hsc' : ∀ m : (∀ i, Fin (n i)), GeneratorPullback.SecScal D'.toPre.P.L (D'.toPre.famφ F α') (DegPre.famε k) (σFB m)
      (D'.toPre.famφB α') (DegPre.famε k) (σB m) (DegPre.prB D'.toPre F).left 1 := fun m =>
    BoxFamScalar.secScal_box hM hM' pD.w (GC.famφ_eq D'.toPre F α') hpr (σFB m) (fun i => σF i (m i)) (σB m)
      (fun i => σ i (m i))
      (fun y J J' hJ hJ' => hσFB m _ (𝟙 _) y J J' hJ hJ')
      (fun y J J' hJ hJ' => hσB m _ (DegPre.prB D'.toPre F).left y J J' hJ hJ')
      (fun _ => 1) 1 (fun y => by rw [Finset.prod_eq_one fun i _ => gs_one _ _, gs_one])
      (fun i => hsc i (m i))
  let e := Fintype.equivFin (∀ i, Fin (n i))
  refine ⟨Fintype.card (∀ i, Fin (n i)), fun l => ∏ i, a i (e.symm l i), fun l => σB (e.symm l),
    fun l => σFB (e.symm l), fun l => hsc' _, fun l => ?_, fun jM => ?_⟩
  · refine le_trans (le_of_eq ?_) (le_val_prod v Finset.univ _ _ fun i => hv i (e.symm l i))
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_div, Int.cast_sum]
  ·
    have H : ∀ (y : (D'.toPre.BF F).left) (J' : ((D'.toPre.BF F).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι),
        Good D'.toPre.P.L y J' → sval (F'.s α') (𝟙 _) y J' =
          ∑ l, gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (e.symm l i)))) * sval (σFB (e.symm l)) (𝟙 _) y J' := by
      intro y J' hJ'
      obtain ⟨J, hJ, -⟩ := exists_good _ hM y (K := Empty) Empty.elim Empty.elim (fun x => x.elim)
        (fun x => x.elim)
      have hle : ∀ (jN : Fin 4 → Fin j → D.toPre.P.L.ι) (jM : Fin 4 → D'.toPre.P.L.ι) (i : Fin j),
          LB.wchart (LB.LinComb D.toPre.P.L (fun i => (pD.pw.pr i).left) (fun _ => 1)) (D'.toPre.famφ F α') jN ⊓
            LB.wchart D'.toPre.P.L (D'.toPre.famφ F α') jM ≤
              prB pD F i ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ F (pD.xe α' i)) (fun a => jN a i) :=
        fun jN jM i => inf_le_left.trans (box_le_of_comp D.toPre.P.L (fun i => (pD.pw.pr i).left)
          (D'.toPre.famφ F α') (D.toPre.famφ F (pD.xe α' i)) (prB pD F i) i (hφ i) jN)
      have hF := BoxFamScalar.box_sval pD.w hφ (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) hle hB (𝟙 _) y hJ hJ'
      have hfac : ∀ i, sval ((Fs i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J =
          ∑ l, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i l))) * sval (σF i l) (𝟙 _ ≫ prB pD F i) y J := by
        intro i
        have hm := hJ.mem (D.toPre.famφ F (pD.xe α' i)) (𝟙 _ ≫ prB pD F i)
        unfold sval
        refine (congrArg (gs (𝟙 _ ≫ prB pD F i) y _) (he i _)).trans ?_
        refine (gs_fsum _ y _ hm _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
        refine (gs_mul _ y _ hm _ _).trans ?_
        unfold DegPre.constBF
        exact congrArg (· * _) (gs_res _ y le_top hm _)
      have hcst : ∀ m : (∀ i, Fin (n i)), ∏ i, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i (m i)))) =
          gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) := by
        intro m
        refine BoxFamScalar.gs_scal_prod (fst (TF (R := V) F) D.toPre.P.A).left
          (fst (TF (R := V) F) D'.toPre.P.A).left (prB pD F) (fun i => ?_) y (fun i => a i (m i))
        unfold prB
        rw [← Over.comp_left]
        simp
      refine (Units.mul_right_inj (∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a)).1 ?_
      refine hF.trans ?_
      rw [Finset.mul_sum]
      simp only [hfac]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [Equiv.sum_comp e.symm (fun m => ((∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a) : _) * (gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) * sval (σFB m) (𝟙 _) y J'))]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.prod_mul_distrib, hcst m, ← hσFB m _ (𝟙 _) y J J' hJ hJ']
      ring
    have key := lin_of_sval hM' _ (fun l => σFB (e.symm l)) H jM
    unfold resTop at key
    unfold DegPre.constBF
    exact key

end GlobalTheory.NuBox
