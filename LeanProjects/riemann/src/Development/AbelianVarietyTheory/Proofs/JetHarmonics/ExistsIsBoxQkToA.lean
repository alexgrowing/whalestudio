import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpBijFOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnboxQk

open GlobalTheory.BoxFamily GlobalTheory.BoxQk GlobalTheory.TorusExt

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def intersection_update_fsHerm_neg_one (i : Fin j) (χ : D.X) : D'.X := pD.xe.symm (Pi.single i χ)

theorem xe_position (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) = Pi.single i χ := pD.xe.apply_symm_apply _

theorem xe_position_self (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i = χ := by
  rw [xe_position, Pi.single_eq_same]

theorem xe_position_ne {i i' : Fin j} (h : i' ≠ i) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i' = 0 := by
  rw [xe_position, Pi.single_eq_of_ne h]

theorem position_add (i : Fin j) (χ χ' : D.X) : intersection_update_fsHerm_neg_one pD i (χ + χ') = intersection_update_fsHerm_neg_one pD i χ + intersection_update_fsHerm_neg_one pD i χ' := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_add, map_add]; rfl

theorem position_zero (i : Fin j) : intersection_update_fsHerm_neg_one pD i 0 = 0 := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_zero, map_zero]

theorem sum_position (x : D'.X) : ∑ i, intersection_update_fsHerm_neg_one pD i (pD.xe x i) = x := by
  apply pD.xe.injective
  rw [map_sum]
  simp only [xe_position]
  exact Finset.univ_sum_single _

theorem exists_gt_at {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (b : TF (R := R) F ⟶ D.P.A)
    (f : D.X → ((TF (R := R) F).left.presheaf.stalk y)ˣ) (f₀ : f 0 = 1)
    (hf : ∀ χ χ', f (χ + χ') * th D y J (cP D _ χ) (cP D _ χ') b = f χ * f χ') :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ, charVal g χ y J = f χ := by
  choose v hv vv using fun χ => exists_gen_val (F := F) D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (f χ)
  refine (exists_gt b v hv (fun _ _ _ _ => rfl) (fun y' J' hJ' => ?_) (fun χ χ' y' J' hJ' => ?_)).imp
    fun _ h => ⟨h.1, fun χ => (h.2 χ y J hJ).trans (vv χ)⟩
  · obtain rfl := pt_eq y y'
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) (hv 0) oneGen_isGen hJ hJ'
      ((vv 0).trans (f₀.trans (val_one _).symm))).trans (val_one _)
    rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · obtain rfl := pt_eq y y'
    refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ' _ _ _))).symm.trans
      (Eq.trans (val_eq_of_val_eq (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hv _) (cubAt_isGen _ _ _))
        (mulGen_isGen _ _ _ _ _ _ _ (hv χ) (hv χ')) hJ hJ'
        (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (val_cubAt hJ _ _ _))).trans ((hf χ χ').trans
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (vv _))).symm))) (val_mul hJ' _ _ _))
    refine (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gt b (χ + χ') h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

section Values

variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
  {J' : ((TF (R := R) F).left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
include hJ

theorem prod_th_factor (i : Fin j) (χ : D.X) (x w : TF (R := R) F ⟶ D'.P.A) :
    ∏ i', th D y J (cP D' _ (intersection_update_fsHerm_neg_one pD i χ) ≫ pD.pw.pr i') (x ≫ pD.pw.pr i') (w ≫ pD.pw.pr i') =
      th D y J (cP D _ χ) (x ≫ pD.pw.pr i) (w ≫ pD.pw.pr i) := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [Finset.prod_eq_single i (fun i' _ h => by rw [cPoint_pr, xe_position_ne pD h, cPoint_zero, C.face]) (by simp),
    cPoint_pr, xe_position_self]

include hJ'

theorem position_val {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (i : Fin j) (χ : D.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' = charVal (g i) χ y J := by
  have e₂ : ∏ i', charVal (g i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = charVal (g i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => by rw [xe_position_ne pD h, charVal_zero _ hJ]) (by simp), xe_position_self]
  exact (box_val pD hJ hJ' h (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem tau_position (hB : D.TauBimult) (i : Fin j) (χ : D.X) (z : D'.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ z) * tauVal D' F z (intersection_update_fsHerm_neg_one pD i χ) y J' =
      tauVal D F (pD.xe z i) χ y J := by
  have e₂ : ∏ i', tauVal D F (pD.xe z i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = tauVal D F (pD.xe z i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => ?_) (by simp), xe_position_self]
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 (pD.xe z i')
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    rw [xe_position_ne pD h]
    exact (tau_symm (𝟙 (TF (R := R) F)) hJ _ _).trans (mul_eq_left.1 t.symm)
  exact (tau_box pD hJ hJ' z (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem exists_comp (hG : GlobalFnsSt) (g' : GtPtF D' F) (i : Fin j) :
    ∃ g : GtPtF D F, g.b = g'.b ≫ pD.pw.pr i ∧ ∀ χ, charVal g χ y J =
      omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' := by
  refine exists_gt_at hJ _ _ ?_ fun χ χ' => ?_
  · rw [position_zero, cPoint_zero, omL_one', charVal_zero g' hJ', _root_.one_mul]
  · have e := th_box pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ (intersection_update_fsHerm_neg_one pD i χ')) g'.b
    rw [prod_th_factor pD hJ, cPoint_pr, xe_position_self, ← cPoint_add, ← position_add] at e
    have e₂ := charVal_add g' hJ' (intersection_update_fsHerm_neg_one pD i χ) (intersection_update_fsHerm_neg_one pD i χ')
    rw [← position_add] at e₂
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₂ - a₁

end Values

theorem exists_unboxGt (hG : GlobalFnsSt) (g' : GtPtF D' F) : ∃ g : Fin j → GtPtF D F, IsBoxGtF pD F g' g := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  choose g hb hv using exists_comp pD hJ hJ' hG g'
  obtain ⟨g'', h⟩ := exists_boxGt pD hG g
  have eb : g''.b = g'.b := pt_ext pD fun i => (h.1 i).trans (hb i)
  have add : ∀ a b, charVal g'' a y J' = charVal g' a y J' → charVal g'' b y J' = charVal g' b y J' →
      charVal g'' (a + b) y J' = charVal g' (a + b) y J' := fun a b ha hb => by
    have e₁ := charVal_add g'' hJ' a b
    rw [eb, ha, hb, ← charVal_add g' hJ' a b] at e₁
    exact mul_right_cancel e₁
  have all : ∀ x, charVal g'' x y J' = charVal g' x y J' := fun x => by
    rw [← sum_position pD x]
    refine Finset.sum_induction _ (fun x => charVal g'' x y J' = charVal g' x y J') add
      ((charVal_zero g'' hJ').trans (charVal_zero g' hJ').symm) fun i _ => ?_
    have e := (position_val pD hJ hJ' h i (pD.xe x i)).trans (hv i _)
    rw [eb] at e
    exact mul_left_cancel e
  obtain rfl : g'' = g' := gt_ext_val_at eb hJ' all
  exact ⟨g, h⟩

theorem unbox_isZero {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (hz : g'.IsZero)
    (i : Fin j) : (g i).IsZero := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isZero_iff_val _).1 hz
  refine (isZero_iff_val _).2 ⟨by rw [← h.1, b, MonObj.one_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b, omL_one, _root_.mul_one]

theorem unbox_isAdd (hG : GlobalFnsSt) {g₁' g₂' g₃' : GtPtF D' F} {g₁ g₂ g₃ : Fin j → GtPtF D F}
    (h₁ : IsBoxGtF pD F g₁' g₁) (h₂ : IsBoxGtF pD F g₂' g₂) (h₃ : IsBoxGtF pD F g₃' g₃)
    (ha : g₁'.IsAdd g₂' g₃') (i : Fin j) : (g₁ i).IsAdd (g₂ i) (g₃ i) := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 ha
  refine (isAdd_iff_val _ _ _).2 ⟨by rw [← h₃.1, ← h₁.1, ← h₂.1, b, MonObj.mul_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  have e := th_box' pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g₁'.b g₂'.b
  rw [prod_th_factor pD hJ, ← b, h₁.1, h₂.1] at e
  rw [← position_val pD hJ hJ' h₁, ← position_val pD hJ hJ' h₂, ← position_val pD hJ hJ' h₃]
  have a₁ := congrArg Additive.ofMul e
  have a₂ := congrArg Additive.ofMul (v (intersection_update_fsHerm_neg_one pD i χ) y J' hJ')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

theorem unbox_isIota (hB : D.TauBimult) {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g)
    {x : D'.X} (hι : GtPtF.IsIota x g') (i : Fin j) : GtPtF.IsIota (pD.xe x i) (g i) := by
  obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 hι
  refine (isIota_iff_val _ _).2 ⟨by rw [← h.1, b, cPoint_pr], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b]
  exact tau_position pD hJ hJ' hB i χ x

theorem exists_unbox (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (p' : QkPt D' F k) :
    ∃ p : Fin j → QkPt D F k, IsBoxQk pD F k p' p := by
  choose ub hub using fun g' : GtPtF D' F => exists_unboxGt pD hG g'
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p'.eq
  exact ⟨fun i => ⟨pD.xe p'.y i, ub p'.g i, ub h i,
    ⟨fun n => ub (gs n) i, unbox_isZero pD (hub _) g₀ i,
      fun n => unbox_isAdd pD hG (hub _) (hub _) (hub _) (gst n) i, congrArg (fun g => ub g i) gl⟩,
    unbox_isIota pD hB (hub _) hι i⟩, rfl, hub _⟩

end Deg

open FieldBaseChange TorsionImage in

theorem image_unique (hL : Laws) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 1 ≤ n)
    (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F n p x)
    (hx' : QkToAkU U.toUnifPre F n p x') : x = x' := by
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

theorem exists_isBoxQk_toA : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ (j : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre j) (pA : IsPowPolAV A' P.A j) (pG : IsPowGrp G' t.G j) (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (k : ℕ), 1 ≤ k → ∀ p' : QkPt D'.toPre F k, ∃ p : Fin j → QkPt P.D.toPre F k, IsBoxQk pD F k p' p ∧ ∀ x' : TFK (R := V) F ⟶ A'.A, QkToAkU U'.toUnifPre F k p' x' → ∀ i, P.ToA F k (p i) (x' ≫ pA.pr i) := by
  intro hL _ _ _ V _ _ _ _ _ E _ _ _ H t P hT j D' A' G' _ _ pD pA pG U' PU F _ _ _ k hk p'
  obtain ⟨p, hp⟩ := exists_unbox pD hL.globalFns P.D.tau_bimult p'
  refine ⟨p, hp, fun x' hx' i => ?_⟩
  obtain ⟨f, hf, -⟩ := hT F k hk
  let x'' : TFK (R := V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ fun i => f (p i))
  have hx : ∀ i, x'' ≫ pA.pr i = f (p i) := fun i => pA.lim.fac (Fan.mk _ fun i => f (p i)) ⟨i⟩
  have h := ProdTorsion.qkToAk_box hL V _ j P.D D' P.A A' t.G G' pD pA pG U' P.U PU
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ P.U)
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ U') F k hk p' p hp x'' (fun i => f (p i)) hx
    (fun i => (hf _ _).2 rfl)
  rw [image_unique hL U' F k hk p' x' x'' hx' h, hx]
  exact (hf _ _).2 rfl

end GlobalTheory.UnboxQk
