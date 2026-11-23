import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SelfUnif

theorem torus_hom_ext {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Subsingleton X] {Z : Over S}
    (a b : Z ⟶ splitTorus S X) : a = b :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun x => by
    rw [Subsingleton.elim x 1, map_one, map_one])

theorem charUnit_zero (S : Scheme.{0}) (X : Type) [AddCommGroup X] : charUnit S X 0 = 1 := by
  have e : toUnits (Multiplicative.ofAdd (0 : X)) = 1 := map_one _
  rw [charUnit, e, map_one, map_one]
  exact (congrArg _ (map_one _)).trans (map_one _)

theorem isPullback_trivial {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Subsingleton X] (G : Over S) [GrpObj G] :
    IsPullback (toUnit (splitTorus S X) ≫ η[G]) (toUnit _) (𝟙 G) η[G] := by
  refine ⟨⟨Category.comp_id _⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => 1) (fun s => ?_) (fun s => toUnit_unique _ _)
    (fun s m _ _ => torus_hom_ext _ _)⟩⟩
  have := s.condition
  rw [Category.comp_id] at this
  rw [this, ← Category.assoc]
  exact congrArg (· ≫ η[G]) (toUnit_unique _ _)

theorem exists_sym {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Spec (CommRingCat.of R))) :
    ∃ sym : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1]), sym.IsGen ∧
      LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym (eSec P.A)) (LB.oneGen P.L) := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have he : eSec P.A ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hi : eSec P.A ≫ (ι[P.A]).left = eSec P.A := congrArg CommaMorphism.left (GrpObj.one_inv (G := P.A))
  obtain ⟨u, hu, hv⟩ := exists_gen P.isLB (φ' := ![(ι[P.A]).left, 𝟙 P.A.left]) (ε' := ![1, -1]) (fun V _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        reassoc_of% hm, hm, Category.assoc, hi, Category.comp_id]
      simp)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ t m)
      (LB.invGen P.L _ _ (LB.pullGen P.L _ _ t (P.A.hom ≫ eSec P.A ≫ m))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, corr_of_val P.isLB fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_one, Category.id_comp,
    reassoc_of% he]
  exact mul_inv_cancel _

variable {X X' : Scheme.{0}} {L : LB X}

theorem exists_spread_pow {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
    (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] [QuasiCompact p] (hL : L.IsLB) (k : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => k))) :
    ∃ d : R, d ≠ 0 ∧ ∃ θ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)),
      ∀ y J, Good L y J → sval θ φ y J = cst (φ ≫ p) y d * sval s (𝟙 _) y J := by
  let N := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)
  have le : ∀ J : PUnit → N.ι, (N.pull φ).U J ≤ LB.wchart L (fun _ : Fin 1 => φ) (J PUnit.unit) :=
    fun J y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 (mem_pull.1 hy) a
  let s' : (N.pull φ).Sec :=
    { f := fun J => resG X' (le J) (s.f (J PUnit.unit))
      compat := fun J J' => fn_ext fun y hy => by
        have hy' : (𝟙 X' : X' ⟶ X') y ∈ (N.pull φ).U J ⊓ (N.pull φ).U J' := hy
        rw [gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy', gs_unit _ y _ hy']
        refine (gs_res (𝟙 X') y (le J) hy'.1 _).trans (Eq.trans ?_ (congrArg _ (gs_res (𝟙 X') y (le J') hy'.2 _)).symm)
        refine (sec_trans s (𝟙 X') y (le J hy.1) (le J' hy.2)).trans (congrArg (fun u => Units.val u * _) ?_)
        refine Eq.trans ?_ (gm_linComb N _ _ (𝟙 X') y J J' hy.1 hy.2).symm
        rw [Fintype.prod_unique, zpow_one]
        refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 X' ≫ φ) y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hy.1)
          (mem_pull.1 hy.2)).symm
        rfl }
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread H (DVR.linComb_isLB L hL _ _) s'
  refine ⟨d, hd, θ, fun y J hJ => ?_⟩
  have hm := hJ.mem (fun _ : Fin 1 => 𝟙 X) φ
  refine (hθ _ y hm).trans (congrArg _ ?_)
  exact gs_res (𝟙 X') y (le fun _ _ => J φ) (mem_pull (L := N) (F := φ) (x := y).2 hm) _

theorem sec_ext_thick {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (hL : L.IsLB)
    {K : Type} [Fintype K] {φ : K → (H.left ⟶ X)} {ε : K → ℤ} (s s' : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ n y J, Good L y J → sval s (fstG I n H).left y J = sval s' (fstG I n H).left y J) : s = s' := by
  refine DVR.SecOps.sec_ext fun j => ?_
  have := (sec_eq_zero_and_hom_eq_of_thickenings R I hI H).1 _ (DVR.linComb_isLB L hL φ ε)
    (DVR.SecOps.secAdd s (DVR.SecOps.secNeg s')) (fun n j => fn_ext fun y hy => by
      choose J hJ using fun ψ : ((Over.map (thick R I n)).obj (thickObj R I n H)).left ⟶ X => exists_chart hL (ψ y)
      refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
      rw [Category.id_comp]
      have a := sec_trans s _ y hy (Good.mem hJ φ _)
      have b := sec_trans s' _ y hy (Good.mem hJ φ _)
      have c := a.trans ((congrArg _ (h n y J hJ)).trans b.symm)
      have c' := (gs_eq _ y _ hy _).symm.trans (c.trans (gs_eq _ y _ hy _))
      refine (gs_eq _ y _ hy _).trans ((congrArg _ ((map_add _ _ _).trans (congrArg _ (map_neg _ _)))).trans
        (((map_add _ _ _).trans (congrArg _ (map_neg _ _))).trans (add_neg_eq_zero.2 c')))) j
  exact add_neg_eq_zero.1 this

end GlobalTheory.SelfUnif

namespace GlobalTheory.SelfUnif

section Ident

variable {X E : Scheme.{0}} {L : LB X} {f p : E ⟶ X}

def IsIdent (w : LB.Iso (L.pull f) (L.pull p)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (i j : L.ι), (r ≫ f) z ∈ L.U i → (r ≫ f) z ∈ L.U j →
    gw w r z i (fun _ => j) = gm (r ≫ f) z _ (L.g i j)

theorem exists_isIdent (hL : L.IsLB) (h : p = f) : ∃ w : LB.Iso (L.pull f) (L.pull p), w.IsGen ∧ IsIdent w := by
  subst h
  exact ⟨idIso (L.pull p), idIso_isGen (pull_isLB hL p), fun Z r z i j hi hj =>
    gm_pull_g L p r z (fun _ => i) (fun _ => j) (mem_pull.2 hi) (mem_pull.2 hj)⟩

theorem IsIdent.trans_gen {w : LB.Iso (L.pull f) (L.pull p)} (hw : IsIdent w) {Y T : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (m m' : T ⟶ Y) (hm : m' = m)
    (q : K → (T ⟶ E)) (hq : ∀ k, m ≫ φ k = q k ≫ f) (y : T) (i j : K → L.ι) (hi : m' y ∈ LB.wchart L φ i)
    (hj : m y ∈ LB.wchart L φ j) :
    gm m' y (LB.wchart L φ i) (t.s i) =
      (∏ k, gw w (q k) y (i k) (fun _ => j k) ^ ε k) * gm m y (LB.wchart L φ j) (t.s j) := by
  subst hm
  refine (gen_trans ht m' y hi hj).trans (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  rw [hw _ (q k) y (i k) (j k) (hq k ▸ Set.mem_iInter.1 hi k) (hq k ▸ Set.mem_iInter.1 hj k), hq k]

end Ident

section Pre

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) [Subsingleton D.X]

theorem c_one (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : toUnit T ≫ D.c χ = 1 := by
  rw [Subsingleton.elim χ 0, IndivisibleSection.c_zero_eq_one, comp_one]

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem exists_coord {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ p χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J, Good D.P.L z J → val t r z J = 1 := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := D.Oφ p χ) (ε' := Oinvε) (fun U _ h => by
      have h2 : toUnit T ≫ η[D.P.A] = 1 := rfl
      have h3 : padd D.P.A p (1 : T ⟶ D.P.A) = p := _root_.mul_one p
      rw [Fin.prod_univ_four]
      simp only [DegPre.Oφ, Oinvε, c_one D T χ, h2, h3]
      simp) (LB.oneGen D.P.L) (oneGen_isGen _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)⟩

theorem exists_gtCoord (e : ℕ) : ∃ g : GtCoord I D e D.P.A, g.q = 𝟙 _ ∧
    ∀ χ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) J, Good D.P.L z J → val (g.t χ) r z J = 1 := by
  choose t ht hv using exists_coord D ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e)
  refine ⟨{
    q := 𝟙 _
    q_hom := inferInstance
    q_flat := inferInstanceAs (Flat (𝟙 _))
    q_surj := inferInstanceAs (Surjective (𝟙 _))
    q_affine := inferInstanceAs (IsAffineHom (𝟙 _))
    i := toUnit _ ≫ η[thickObj R I e D.P.A]
    i_hom := inferInstance
    isKernel := isPullback_trivial _
    t := t
    t_gen := ht
    t_mul := fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_
    t_unit := fun χ => corr_of_val D.P.isLB fun y J hJ => ?_
    t_weight := fun χ => corr_of_val D.P.isLB fun y J hJ => ?_ }, rfl, hv⟩
  · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (val_cub D.cub (𝟙 _) hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ)).symm)
    rw [Category.id_comp, c_one, (isCub_cubV D.cub hJ).face]
  · exact (val_pull hJ _ _ _).trans ((hv _ _ _ y J hJ).trans (val_one _).symm)
  · refine (val_pull hJ _ _ _).trans ((hv _ _ _ y J hJ).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm))
    refine Eq.symm ((congrArg₂ (· * ·) ?_ ((val_pull hJ _ _ _).trans (hv _ _ _ y J hJ))).trans (_root_.mul_one 1))
    obtain rfl : χ = 0 := Subsingleton.elim _ _
    refine (congrArg (gm _ y _) ?_).trans (map_one _)
    refine (congrArg (fun u => res _ (pullU _ ⊤ u)) (charUnit_zero _ _)).trans ?_
    exact (congrArg _ (map_one _)).trans (map_one _)

def selfGt (e : ℕ) : GtCoord I D e D.P.A := (exists_gtCoord I D e).choose

theorem selfGt_pG (e : ℕ) : (selfGt I D e).pG = fstG I e D.P.A := by
  refine Over.OverMorphism.ext ?_
  show (selfGt I D e).q.left ≫ _ = _
  rw [show (selfGt I D e).q = 𝟙 _ from (exists_gtCoord I D e).choose_spec.1]
  exact Category.id_comp _

theorem selfGt_pG_left (e : ℕ) : (selfGt I D e).pG.left = (fstG I e D.P.A).left :=
  congrArg CommaMorphism.left (selfGt_pG I D e)

theorem selfTorusExtensionCoord_values_eq_one (e : ℕ) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ _) (z : Z) {J} (hJ : Good D.P.L z J) :
    val ((selfGt I D e).t χ) r z J = 1 := (exists_gtCoord I D e).choose_spec.2 χ Z r z J hJ

def selfW (e : ℕ) : LB.Iso (D.P.L.pull (fstG I e D.P.A).left) (D.P.L.pull (selfGt I D e).pG.left) :=
  (exists_isIdent D.P.isLB (selfGt_pG_left I D e)).choose

theorem selfW_gen (e : ℕ) : (selfW I D e).IsGen := (exists_isIdent D.P.isLB (selfGt_pG_left I D e)).choose_spec.1

theorem selfW_ident (e : ℕ) : IsIdent (selfW I D e) := (exists_isIdent D.P.isLB (selfGt_pG_left I D e)).choose_spec.2

end Pre

open UnifPullRig in

def selfPre {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) [Subsingleton D.toPre.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A)
    (hA : IsMonHom eA.hom)
    (hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen) :
    UnifPre I D A D.toPre.P.A where
  smooth := D.toPre.P.isAb.smooth
  separated := by have := D.toPre.P.isAb.proper; infer_instance
  gen := eA
  gen_hom := hA
  LG := ⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩
  cubG := D.toPre.cub
  symG := D.toPre.sym
  symG_gen := D.toPre.sym_gen
  symG_rig := D.toPre.sym_rig
  ext := hw
  gt := selfGt I D.toPre
  gt_q e := by rw [selfGt_pG_left, selfGt_pG_left, thickMap_fstG]
  gt_t e χ := corr_of_val D.toPre.P.isLB fun y J hJ =>
    (val_pull hJ _ _ _).trans ((selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).trans (selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).symm)
  w := selfW I D.toPre
  w_gen := selfW_gen I D.toPre
  w_rig e := by
    rintro ⟨qM, qL⟩ V h₁ h₂ h₃
    refine unit_ext fun y hy => ?_
    have E := (selfW_ident I D.toPre e).trans_gen (K := PUnit) D.toPre.rig_gen (thick R I e) _ rfl
      (fun _ => eSec (thickObj R I e D.toPre.P.A)) (fun _ => (eSec_fstG I e _).symm) y qM qL (h₃ hy) (h₂ hy)
    rw [Fintype.prod_unique, zpow_one] at E
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ _ y h₁ hy _)
      (gm_res_pull _ _ y h₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ _ y h₃ hy _).symm))
    rw [Category.id_comp, Category.id_comp]
    exact E.symm
  w_even e jS jT _ _ V h₁ h₂ h₃ h₄ := by
    refine unit_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := EvenPull.even_stalk (selfW I D.toPre e) D.toPre.sym D.toPre.sym jS jT V h₁ h₂ h₃ h₄ (𝟙 _) y hy
    refine k₁.trans (Eq.trans ?_ k₂.symm)
    have E := (selfW_ident I D.toPre e).trans_gen D.toPre.sym_gen _ _ (selfGt_pG_left I D.toPre e)
      ![(ι[thickObj R I e D.toPre.P.A]).left, 𝟙 _] (Fin.forall_fin_two.2 ⟨(EvenPull.inv_fst _ _).symm,
        (Category.comp_id _).trans (Category.id_comp _).symm⟩) y jT jS (h₁ hy) (h₄ hy)
    rw [Fin.prod_univ_two] at E
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at E
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    refine (congrArg (· * _) E).trans ?_
    rw [mul_right_comm]
    exact congrArg (· * _) (inv_mul_cancel_right _ _)
  w_cub e T x jL jM _ _ := by
    refine (WCub.clause_iff (WCub.tri (thick R I e) (selfGt I D.toPre e).pG x)
      (WCub.tri (thick R I e) (fstG I e D.toPre.P.A) x)
      (fun k : thK => (psum (thickObj R I e D.toPre.P.A) x k.down).left) _ _ _ (D.toPre.cub.t.s jM)
      (D.toPre.cub.t.s jL) (fun k => (selfW I D.toPre e).s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hL _ => ?_
    exact (selfW_ident I D.toPre e).trans_gen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.isGen _ _
      (congrArg (fun q => WCub.tri (thick R I e) q x) (selfGt_pG I D.toPre e)) _
      (WCub.tri_thφ (thick R I e) (fstG I e D.toPre.P.A) x (𝟙 _) (Category.id_comp _).symm) y jM jL hB hL
  w_compat e := by
    rintro ⟨qM, qL⟩ V h₁ h₂
    refine unit_ext fun y hy => ?_
    have hM : (fstG I e D.toPre.P.A).left y ∈ D.toPre.P.L.U (qM PUnit.unit) :=
      (congrArg (fun q => q y ∈ _) (selfGt_pG_left I D.toPre e)).mp (mem_pull.1 (h₂ hy).1)
    have hL : (fstG I e D.toPre.P.A).left y ∈ D.toPre.P.L.U (qL PUnit.unit) := mem_pull.1 (h₂ hy).2
    have t := thickMap_fstG I e D.toPre.P.A
    have a := selfW_ident I D.toPre e _ (𝟙 _) y _ _ hM hL
    have b := selfW_ident I D.toPre (e + 1) _ (thickMap R I e _) y _ _
      ((congrArg (fun q => q y ∈ _) t).mpr hM) ((congrArg (fun q => q y ∈ _) t).mpr hL)
    rw [t] at b
    rw [Category.id_comp] at a
    refine (gm_res_pull _ _ y h₁ hy _).trans (Eq.trans ?_ (gm_res _ y h₂ hy _).symm)
    rw [Category.id_comp]
    exact b.trans a.symm

end GlobalTheory.SelfUnif

namespace GlobalTheory.SelfUnif

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) [Subsingleton D.toPre.X]

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    val (D.toPre.tau 0 0) r z J = 1 ∧ val (D.toPre.psi 0) r z J * val D.toPre.rigK r z J = 1 := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ jK R)
  let ρ : T ⟶ TK R := Over.homMk r rfl
  have v : ∀ a b : D.toPre.X, val (D.toPre.tau a b) r z J = val (D.toPre.tau 0 0) r z J := fun a b => by
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
  have v' : ∀ a : D.toPre.X, val (D.toPre.psi a) r z J = val (D.toPre.psi 0) r z J := fun a => by
    rw [Subsingleton.elim a 0]
  have c := val_cub D.toPre.cub ρ (z := z) hJ (toUnit _ ≫ D.toPre.c 0) (toUnit _ ≫ D.toPre.c 0) (toUnit _ ≫ D.toPre.c 0)
  rw [show cubV D.toPre.cub (T := T) z J (ρ ≫ toUnit _ ≫ D.toPre.c 0) (ρ ≫ toUnit _ ≫ D.toPre.c 0)
    (ρ ≫ toUnit _ ≫ D.toPre.c 0) = 1 by rw [c_one, comp_one, (isCub_cubV D.toPre.cub (T := T) hJ).face]] at c
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ _) c)).symm.trans
    ((val_corr hJ (D.tau_bimult 0 0 0) r).trans (val_mul hJ _ _ _))
  have h := (mul_left_cancel e).symm
  refine ⟨h, ?_⟩
  have t := (val_mul hJ _ _ r).symm.trans h
  rw [val_mul hJ, val_mul hJ, val_inv, val_inv, v', mul_inv_cancel, _root_.one_mul, ← mul_inv] at t
  exact inv_eq_one.1 t

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem prod_famφ (k : ℕ) (α : D.toPre.X) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h (DegPre.famφ D.toPre F α i) ^ DegPre.famε k i = h (DegPre.prB D.toPre F).left ^ (k : ℤ) := by
  have h2 : toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A] = 1 := rfl
  have h3 : padd D.toPre.P.A (DegPre.prB D.toPre F) 1 = DegPre.prB D.toPre F := _root_.mul_one _
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφ, DegPre.famε, c_one D.toPre _ α, h2, h3]
  simp [zpow_sub]

theorem prod_famφB (k : ℕ) (α : D.toPre.X) {U : Type} [CommGroup U]
    (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h (D.toPre.famφB α i) ^ DegPre.famε k i = h (𝟙 _) ^ (k : ℤ) := by
  have h2 : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
  have h3 : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 _ := _root_.mul_one _
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, c_one D.toPre _ α, h2, h3]
  simp [zpow_sub]

theorem famFE (hG : GlobalFnsSt) (k : ℕ)
    (s : ∀ α : D.toPre.X, LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) :
    DegPre.FamFE D.toPre F k s := by
  intro mu α u hu hc
  obtain rfl : mu = 0 := Subsingleton.elim _ _
  obtain rfl : α = 0 := Subsingleton.elim _ _
  have ht : (DegPre.trF D.toPre F 0).left = 𝟙 _ := by
    have h3 : padd D.toPre.P.A (DegPre.prB D.toPre F) 1 = DegPre.prB D.toPre F := _root_.mul_one _
    rw [DegPre.trF, c_one, h3, lift_fst_snd]; rfl
  refine (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_
  have hv : val u (𝟙 _) y J = 1 := by
    refine (gen_unique' D.toPre.P.isLB (fun U _ h => ?_) (fst (TF (R := R) F) D.toPre.P.A).left
      (DegPre.zF D.toPre F).left (by rw [← Over.comp_left, DegPre.zF, lift_fst]; rfl) (DVR.surj_appTop D.toPre F hG) hu
      (oneGen_isGen _) (fun z N hN => ?_) _ _ y J hJ).trans (val_one _)
    · refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
      simp only [DegPre.deltaφ, DegPre.deltaε, Sum.elim_inl, Sum.elim_inr, ht, Category.id_comp, zpow_neg,
        Finset.prod_inv_distrib, prod_famφ, mul_inv_cancel]
    · have e := (val_pull hN _ _ _).symm.trans ((val_corr hN hc (𝟙 _)).trans (val_pull hN _ _ _))
      obtain ⟨a, b⟩ := val_tau D (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z hN
      rw [Category.id_comp, val_mul hN, val_mul hN, DVR.TWM.val_powGen, DVR.TWM.val_powGen, a, _root_.mul_one,
        ← mul_pow, b, one_pow] at e
      exact e.trans (val_one _).symm
  have v : ∀ a : D.toPre.X, sval (s a) (𝟙 _) y J = sval (s 0) (𝟙 _) y J := fun a => by rw [Subsingleton.elim a 0]
  rw [hv, ht, Category.id_comp, v, Units.val_one, _root_.mul_one]

end Fam

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) [Subsingleton D.toPre.X]
  (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A)
  (hA : IsMonHom eA.hom)
  (hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen)

theorem wv_sv (e k : ℕ) (σ : H0 D.toPre.P.L k) (y : (thickObj R I e D.toPre.P.A).left) {J}
    (hJ : Good D.toPre.P.L y J) (jL : D.toPre.P.L.ι) (hL : DVR.fGl I D.toPre.P.A e y ∈ D.toPre.P.L.U jL) :
    (DVR.wv (selfPre D A eA hA hw) e (𝟙 _) y (J (DVR.fGl I D.toPre.P.A e)) jL ^ k).val *
      DVR.sv (selfPre D A eA hA hw) k σ (DVR.fGl I D.toPre.P.A e) y jL = sval σ (DVR.fGl I D.toPre.P.A e) y J := by
  have a := selfW_ident I D.toPre e _ (𝟙 _) y _ _ (hJ (DVR.fGl I D.toPre.P.A e)) hL
  have b := sec_trans σ (DVR.fGl I D.toPre.P.A e) y (j := fun _ => J (DVR.fGl I D.toPre.P.A e)) (j' := fun _ => jL)
    (Set.mem_iInter.2 fun _ => hJ (DVR.fGl I D.toPre.P.A e)) (Set.mem_iInter.2 fun _ => hL)
  rw [trF, Fintype.prod_unique, zpow_natCast] at b
  exact (congrArg (fun u : ((thickObj R I e D.toPre.P.A).left.presheaf.stalk y)ˣ => (u ^ k).val *
    DVR.sv (selfPre D A eA hA hw) k σ (DVR.fGl I D.toPre.P.A e) y jL) a).trans b.symm

theorem expandsAt_iff (e k : ℕ) (σ : H0 D.toPre.P.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    (selfPre D A eA hA hw).ExpandsAt e k σ f ↔ ∀ (y : (thickObj R I e D.toPre.P.A).left) J, Good D.toPre.P.L y J →
      sval σ (DVR.fGl I D.toPre.P.A e) y J = sval (f 0) (DVR.fGl I D.toPre.P.A e) y J := by
  have hp : DVR.pGl (selfPre D A eA hA hw) e = DVR.fGl I D.toPre.P.A e := selfGt_pG_left I D.toPre e
  have ht : ∀ α y J, Good D.toPre.P.L y J → val (DVR.tG (selfPre D A eA hA hw) e α) (𝟙 _) y J = 1 :=
    fun α y J hJ => selfTorusExtensionCoord_values_eq_one I D.toPre e α _ y hJ
  constructor
  · intro h y J hJ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val (selfPre D A eA hA hw) e k σ f h
    obtain ⟨h₀, h₁⟩ := hS _ (𝟙 _) y J hJ
    have E := h₁ _ (hJ (DVR.fGl I D.toPre.P.A e))
    rw [Category.id_comp, Category.id_comp, Finset.sum_eq_single 0
      (fun b _ hb => (hb (Subsingleton.elim _ _)).elim) (fun h0 => by
        rw [← Category.id_comp (DVR.pGl _ e), h₀ 0 h0, zero_mul]), ht 0 y J hJ, Units.val_one, _root_.mul_one] at E
    rw [hp] at E
    exact (wv_sv D A eA hA hw e k σ y hJ _ (hJ _)).symm.trans E
  · intro h
    refine DVR.expandsAt_of_val (selfPre D A eA hA hw) e k σ f {0} fun y J hJ => ⟨fun α hα => (hα (Finset.mem_singleton.2
      (Subsingleton.elim _ _))).elim, fun jL hL => ?_⟩
    rw [Finset.sum_singleton, ht 0 y J hJ, Units.val_one, _root_.mul_one, hp]
    exact (wv_sv D A eA hA hw e k σ y hJ jL hL).trans (h y J hJ)

theorem expandsAll_iff [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) (σ : H0 D.toPre.P.L k)
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    (∀ e, (selfPre D A eA hA hw).ExpandsAt e k σ f) ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) J,
      Good D.toPre.P.L z J → sval σ r z J = sval (f 0) r z J := by
  refine ⟨fun h => ?_, fun h e => (expandsAt_iff D A eA hA hw e k σ f).2 fun y J hJ => h _ _ y J hJ⟩
  obtain ⟨σ', hσ⟩ := exists_sec D.toPre.P.isLB (φ' := fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by rw [prod_famφB, Fintype.prod_unique]) (f 0)
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  obtain rfl : σ = σ' := sec_ext_thick hI D.toPre.P.A D.toPre.P.isLB σ σ' fun n y J hJ =>
    ((expandsAt_iff D A eA hA hw n k σ f).1 (h n) y J hJ).trans (hσ _ _ y J hJ).symm
  exact hσ

omit [Subsingleton D.toPre.X] in
theorem exists_genericIso : ∃ κ : pullback D.toPre.P.A.hom (jK R) ≅ (DegPre.BF D.toPre (FractionRing R)).left,
    κ.hom ≫ (DegPre.prB D.toPre (FractionRing R)).left = pullback.fst D.toPre.P.A.hom (jK R) := by
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _
  exact ⟨pullbackSymmetry _ _ ≪≫ pullback.congrHom e.symm rfl,
    (Category.assoc _ _ _).trans ((congrArg _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _))).trans
      (pullbackSymmetry_hom_comp_snd _ _))⟩

theorem expands_iff [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    (κ : pullback D.toPre.P.A.hom (jK R) ≅ (DegPre.BF D.toPre (FractionRing R)).left)
    (hκ : κ.hom ≫ (DegPre.prB D.toPre (FractionRing R)).left = pullback.fst D.toPre.P.A.hom (jK R)) (k : ℕ)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => pullback.fst D.toPre.P.A.hom (jK R)) (fun _ => (k : ℤ))))
    (F : Fam D.toPre (FractionRing R) k) :
    (selfPre D A eA hA hw).Expands k s F ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback D.toPre.P.A.hom (jK R)) (z : Z) J,
      Good D.toPre.P.L z J → sval s r z J = sval (F.s 0) (r ≫ κ.hom) z J := by
  have hL := D.toPre.P.isLB
  have hb : κ.hom ≫ (DegPre.BF D.toPre (FractionRing R)).hom = pullback.snd D.toPre.P.A.hom (jK R) ≫ jK R := by
    rw [← Over.w (DegPre.prB D.toPre (FractionRing R)), ← Category.assoc, hκ, pullback.condition]
  have gc : ∀ {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R), gs r z ⊤ (scal p a) = cst (r ≫ p) z a :=
    fun p r z a => gs_pull r p z ⊤ trivial _
  constructor
  · rintro ⟨d, hd, σ, f, h₁, h₂, h₃⟩ Z r z J hJ
    have a := BoxFamScalar.sval_of_secScal (L := D.toPre.P.L) h₁ r z hJ
    have b := BoxFamScalar.sval_of_secScal (h₂ 0) (r ≫ κ.hom) z hJ
    have c := (expandsAll_iff D A eA hA hw hI k σ f).1 h₃ _ (r ≫ pullback.fst D.toPre.P.A.hom (jK R)) z J hJ
    rw [Category.assoc, hκ, gc, Category.assoc, hb] at b
    rw [gc] at a
    have hu : IsUnit (cst (r ≫ pullback.snd D.toPre.P.A.hom (jK R) ≫ jK R) z d) := by
      have := SecSpread.isUnit_cst (K := FractionRing R) (φ := r ≫ pullback.fst D.toPre.P.A.hom (jK R))
        (p := D.toPre.P.A.hom) (π := r ≫ pullback.snd D.toPre.P.A.hom (jK R))
        (by rw [Category.assoc, Category.assoc, pullback.condition]) z hd
      rwa [Category.assoc, pullback.condition] at this
    exact hu.mul_left_cancel (a.symm.trans (c.trans b))
  · intro h
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.proper
    obtain ⟨d, hd, θ, hθ⟩ := exists_spread_pow (K := FractionRing R)
      (IsPullback.of_hasPullback D.toPre.P.A.hom (jK R)) hL k s
    choose f hf using fun α : D.toPre.X => exists_sec hL (φ' := D.toPre.famφB α) (ε' := DegPre.famε k)
      (fun U _ h => by rw [prod_famφB, Fintype.prod_unique]) θ
    have h₁ : GeneratorPullback.SecScal D.toPre.P.L _ _ s _ _ θ (pullback.fst D.toPre.P.A.hom (jK R))
        (scal (pullback.snd D.toPre.P.A.hom (jK R) ≫ jK R) d) := BoxFamScalar.secScal_of_pointwise hL fun y J hJ => by
      rw [gc, Category.id_comp, Category.id_comp, ← pullback.condition]
      exact hθ y J hJ
    refine ⟨d, hd, θ, f, h₁, fun α => BoxFamScalar.secScal_of_pointwise hL fun y J hJ => ?_,
      (expandsAll_iff D A eA hA hw hI k θ f).2 fun Z r z J hJ => (hf 0 Z r z J hJ).symm⟩
    obtain rfl : α = 0 := Subsingleton.elim _ _
    have a := BoxFamScalar.sval_of_secScal h₁ κ.inv y hJ
    rw [h _ κ.inv y J hJ, gc, ← hκ, ← hb, κ.inv_hom_id_assoc, κ.inv_hom_id_assoc, κ.inv_hom_id] at a
    rw [hf 0 _ _ y J hJ, gc, Category.id_comp, Category.id_comp]
    exact a

theorem expBij (hG : GlobalFnsSt) [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) :
    (selfPre D A eA hA hw).ExpBij k := by
  obtain ⟨κ, hκ⟩ := exists_genericIso D
  have hκ' : κ.inv ≫ pullback.fst D.toPre.P.A.hom (jK R) = (DegPre.prB D.toPre (FractionRing R)).left := by
    rw [← hκ, κ.inv_hom_id_assoc]
  have hL := D.toPre.P.isLB
  have key := expands_iff D A eA hA hw hI κ hκ k
  refine ⟨fun s => ?_, fun F => ?_⟩
  · choose t ht using fun α : D.toPre.X => IndivisibleSection.exists_pull_val (L := D.toPre.P.L) hL s κ.inv
      (φ' := DegPre.famφ D.toPre (FractionRing R) α) (ε' := DegPre.famε k)
      (fun U _ h => by rw [prod_famφ, Fintype.prod_unique, hκ'])
    refine ⟨⟨t, famFE D _ hG k t⟩, (key s _).2 fun Z r z J hJ => ?_, fun F hF => DVR.fam_ext fun α j => ?_⟩
    · refine Eq.trans ?_ (ht 0 Z _ z J hJ).symm
      rw [Category.assoc, κ.hom_inv_id, Category.comp_id]
    · obtain rfl : α = 0 := Subsingleton.elim _ _
      refine sec_ext_val hL (fun y J hJ => ?_) j
      have a := (key s F).1 hF _ κ.inv y J hJ
      rw [κ.inv_hom_id] at a
      refine a.symm.trans (Eq.trans ?_ (ht 0 _ _ y J hJ).symm)
      rw [Category.id_comp]
  · obtain ⟨s, hs⟩ := IndivisibleSection.exists_pull_val hL (F.s 0) κ.hom
      (φ' := fun _ : Fin 1 => pullback.fst D.toPre.P.A.hom (jK R)) (ε' := fun _ => (k : ℤ))
      (fun U _ h => by rw [prod_famφ D _ k 0 (fun ψ => h (κ.hom ≫ ψ)), Fintype.prod_unique, hκ])
    refine ⟨s, (key s F).2 hs, fun s' hs' => DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)⟩
    exact ((key s' F).1 hs' _ _ y J hJ).trans (hs _ _ y J hJ).symm

end Exp

theorem exists_degData (hC : CubeSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (P : PolAV (Spec (CommRingCat.of R))) :
    ∃ D : DegData R I, D.toPre.P = P ∧ Subsingleton D.toPre.X := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (hC _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := exists_sym P
  let D : DegPre R :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := PUnit
      c := fun _ => η[P.A]
      c_add := fun _ _ => by
        have : η[P.A] = (1 : 𝟙_ _ ⟶ P.A) := by simp [Hom.one_def]
        rw [this]; exact (_root_.mul_one _).symm
      psi := fun _ => LB.invGen P.L _ _ (LB.pullGen P.L _ _ rig (toUnit (TK R)).left)
      psi_gen := fun _ => DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hrig _) }
  have vp : ∀ (a : D.X) y J, val (D.psi a) (𝟙 _) y J = (val D.rigK (𝟙 _) y J)⁻¹ := fun a y J => val_inv _ _
  have vt : ∀ (a b : D.X) y J, Good P.L y J → val (D.tau a b) (𝟙 _) y J = 1 := fun a b y J hJ => by
    refine (val_mul hJ _ _ _).trans ?_
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, vp (a + b)]
    simp
  refine ⟨⟨D, fun χ => corr_of_val P.isLB fun y J hJ => ?_, fun a a' b => corr_of_val P.isLB fun y J hJ => ?_,
    fun χ h => (h rfl).elim, fun n => Set.toFinite _⟩, rfl, ⟨fun _ _ => rfl⟩⟩
  · have a := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hsr (toUnit (TK R)).left).trans (val_one _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_)).trans (_root_.mul_one _))
    rw [Category.id_comp]
    exact a
  · have c := val_cub cub (𝟙 (TK R)) hJ (toUnit _ ≫ η[P.A]) (toUnit _ ≫ η[P.A]) (toUnit _ ≫ η[P.A])
    rw [Category.id_comp] at c
    have c' := c.trans ((isCub_cubV cub hJ).face _ _)
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt _ _ y J hJ) c')).trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt _ _ y J hJ) (vt _ _ y J hJ))).symm

end GlobalTheory.SelfUnif

namespace GlobalTheory

open SelfUnif in

theorem exists_unif_abelianScheme : GlobalFnsSt → SecBaseChangeSt → CubeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj P.A ≅ A.A), IsMonHom eA.hom → (∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom (jK R))), w.IsGen) → ∃ D : DegData R I, D.toPre.P = P ∧ Subsingleton D.toPre.X ∧ Nonempty (Unif I D A P.A) := by
  intro hG _ hC R _ _ _ _ I _ P A eA hA hw
  obtain ⟨D, rfl, hX⟩ := exists_degData hC I P
  exact ⟨D, rfl, hX, ⟨⟨selfPre D A eA hA hw, fun k _ =>
    expBij D A eA hA hw hG (IsAdicComplete.le_jacobson_bot I) k⟩⟩⟩

end GlobalTheory
