import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

variable (B') in

abbrev sw2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
  ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]

theorem lift_comp_squareFactorIdentity_eq_lift {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 0 = (lift a b).left := by
  show (lift a b).left ≫ (lift (fst B' B') (snd B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem lift_comp_squareFactorSwap_eq_lift_swap {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 1 = (lift b a).left := by
  show (lift a b).left ≫ (lift (snd B' B') (fst B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem formEq_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => sw2 B' k ≫ β₂) (flatε lamε ![1, -1]) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  intro U _ h
  rw [GlobalTheory.LamBiext.prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
  show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
    (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
  rw [β₂_lift, β₂_lift, GlobalTheory.LamBiext.prod_lam, GlobalTheory.LamBiext.prod_lam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_gen_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {M : LB B.left} (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M) (fun k => sw2 B' k ≫ β₂) ![1, -1]), t.IsGen ∧
      ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι), Good M z J →
        val (L := abelian₂ B M) t r z (ind B J) = 1 := by
  obtain ⟨g, hg, hv⟩ := exists_gen hM (formEq_sw hβ hsq) (LB.oneGen M) (oneGen_isGen _)
  refine ⟨GlobalTheory.LamBiext.nest M (lamφ B) lamε (fun k => sw2 B' k ≫ β₂) ![1, -1] g, nest_isGen hg,
    fun r z J hJ => ?_⟩
  refine (val_nest hg r (good_ind hJ) hJ).trans ?_
  simp only [adj_ind hM hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (hv _ r z J hJ).trans (val_one r)

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.Mum.Two

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

theorem isoVal_swap (hB' : IsAbelianScheme B') {M : LB B.left} {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB)
    {f : S' ⟶ S} {f₁ : S' ⟶ S₁} {β : B'.left ⟶ B.left} {β₁ : B'.left ⟶ B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (hβ : IsGrpPullback B' B f β) (hβ₁ : IsGrpPullback B' B₁ f₁ β₁) (hsq : IsSquare β β₂) (hsq₁ : IsSquare β₁ β₂')
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) (hw : w.IsGen) {T : Over S'} (x y : T ⟶ B')
    (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.ι) (J' : (T.left ⟶ B.left) → M.ι) (hJ : Good M₁ z J)
    (hJ' : Good M z J') :
    isoVal w (lift x y).left z J J' = isoVal w (lift y x).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have hL' : ((abelian₂ B M).pull β₂).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _
  obtain ⟨t, ht, hvt⟩ := exists_gen_sw hβ₁ hsq₁ hM₁
  obtain ⟨g, hg, hvg⟩ := exists_gen_sw hβ hsq hM
  let c := chartPullLinComb (abelian₂ B M) β₂ (sw2 B') (fun k => sw2 B' k ≫ β₂) ![1, -1] (𝟙 _)
    (fun k => (Category.id_comp _).symm)
  have ha : (cGen c g).IsGen := cGen_isGen c hg
  have good_P : ∀ {Z : Scheme.{0}} {z₀ : Z} {J₀ : (Z ⟶ B.left) → M.ι}, Good M z₀ J₀ →
      Good ((abelian₂ B M).pull β₂) z₀ (fun q _ => ind B J₀ (q ≫ β₂)) :=
    fun hJ₀ q => mem_pull.2 (good_ind hJ₀ (q ≫ β₂))
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B.left) → M.ι), Good M z₀ J₀ →
      val (cGen c g) r z₀ (fun q _ => ind B J₀ (q ≫ β₂)) = 1 := by
    intro Z r z₀ J₀ hJ₀
    rw [← hvg r z₀ J₀ hJ₀, val_of g r z₀ (ind B J₀) (fun k => ind B J₀ ((r ≫ sw2 B' k) ≫ β₂))
      (fun k => by rw [Category.assoc])]
    exact gm_res r z₀ _ ((good_P hJ₀).mem _ r) _
  have gw_iso : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (φ : (G2 B').left ⟶ (G2 B').left) (z₀ : Z)
      (J₀ : (Z ⟶ B₁.left) → M₁.ι) (J₀' : (Z ⟶ B.left) → M.ι),
      gw w (r ≫ φ) z₀ (ind B₁ J₀ (r ≫ φ ≫ β₂')) (fun _ => ind B J₀' ((r ≫ φ) ≫ β₂)) =
        isoVal w (r ≫ φ) z₀ J₀ J₀' := by
    intro Z r φ z₀ J₀ J₀'
    have e₁ : ind B₁ J₀ (r ≫ φ ≫ β₂') = fun I => J₀ ((r ≫ φ) ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left) :=
      funext fun I => congrArg J₀ (by simp only [Category.assoc])
    have e₂ : ind B J₀' ((r ≫ φ) ≫ β₂) = fun I => J₀' ((r ≫ φ) ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
      funext fun I => congrArg J₀' (by simp only [Category.assoc])
    rw [e₁, e₂]; rfl
  have Fp : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B₁.left) → M₁.ι)
      (J₀' : (Z ⟶ B.left) → M.ι),
      pw w (sw2 B') ![1, -1] r z₀ (fun k => ind B₁ J₀ (r ≫ sw2 B' k ≫ β₂'))
        (fun k => (fun (q : Z ⟶ (G2 B').left) (_ : PUnit) => ind B J₀' (q ≫ β₂)) (r ≫ sw2 B' k)) =
        isoVal w (r ≫ sw2 B' 0) z₀ J₀ J₀' * (isoVal w (r ≫ sw2 B' 1) z₀ J₀ J₀')⁻¹ := by
    intro Z r z₀ J₀ J₀'
    unfold pw
    rw [Fin.prod_univ_two]
    rw [gw_iso r (sw2 B' 0) z₀ J₀ J₀', gw_iso r (sw2 B' 1) z₀ J₀ J₀']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg]
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have E := rigid_pw w hw hL hL' (sw2 B') ![1, -1] ha ht _ _ he2
    (surj_comp (surj_snd hG hB' _) (hG _ _ hB').2) (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM₁ y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      refine ⟨ind B₁ J₁, fun q _ => ind B J₁' (q ≫ β₂), good_ind hJ₁, good_P hJ₁', ?_⟩
      rw [hvt _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, mul_inv_cancel, _root_.mul_one])
    T.left (lift x y).left z (ind B₁ J) (fun q _ => ind B J' (q ≫ β₂)) (good_ind hJ) (good_P hJ')
  rw [hvt _ z J hJ, Fp, Fa _ z J' hJ', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, _root_.mul_one] at E
  exact mul_inv_eq_one.1 E.symm

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart

theorem periodConst_symm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁ hfin hloc hκ hpb hpb' hsq hsq'
    x hx w₁ q hgen hper hnorm a b
  have hAb : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback D.toPre.P.isAb hpb
  obtain ⟨κK, hκK⟩ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ := by
    have hi : Function.Injective ((algebraMap V₁ (FractionRing V₁)).comp f₁) :=
      (IsFractionRing.injective V₁ (FractionRing V₁)).comp hf₁
    obtain ⟨g, eg⟩ : ∃ g : FractionRing V →+* FractionRing V₁,
        g.comp (algebraMap V (FractionRing V)) = (algebraMap V₁ (FractionRing V₁)).comp f₁ :=
      ⟨IsLocalization.lift (M := nonZeroDivisors V) (g := (algebraMap V₁ (FractionRing V₁)).comp f₁) fun y =>
        IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
    refine ⟨spMap g, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eg]
  let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  have h₁ := hper κK hκK a b z J J' hJ hJ'
  have h₂ := hper κK hκK b a z J J' hJ hJ'
  rw [GlobalTheory.Mum.RosatiSymmetry.val_tau_symm D.toPre hJ' κK,
    val_corr hJ (corr_of_val L.T.M.isLB (L.T.τ₀_symm ((n : ℤ) • b) ((n : ℤ) • a))),
    GlobalTheory.TChart.SwapIso.isoVal_swap hAb D.toPre.P.isLB L.T.M.isLB hpb hpb' hsq hsq' w₁ hgen
      (toUnit (TK V₁) ≫ x b) (toUnit (TK V₁) ≫ x a) z J J' hJ hJ'] at h₂
  have hq := mul_right_cancel (h₁.symm.trans h₂)
  have hs : Subsingleton (TK V₁).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing V₁)))
  have eu : unitOn (q a b) = unitOn (q b a) := unit_ext fun y _ => by rw [Subsingleton.elim y z]; exact hq
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv).1 eu

end GlobalTheory.TChart
