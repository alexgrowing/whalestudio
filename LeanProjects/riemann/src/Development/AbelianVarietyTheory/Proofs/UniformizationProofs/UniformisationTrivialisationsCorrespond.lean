import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def LevelOneEq (D : DegPre R) (f : ∀ α : D.X, D.SecB 1 α) : Prop :=
  ∀ (mu α : D.X), α = 0 → ∀ (T : Over (Spec (CommRingCat.of R))) (κ : T ⟶ TF (R := R) (FractionRing R))
    (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval (f mu) y.left z J = sval (f α) (y * cP D T mu).left z J *
      (val (D.psi mu) (κ.left ≫ jFK (R := R) (FractionRing R)) z J * val D.rig T.hom z J).val

theorem levelOneEq_of_fam (hG : GlobalFnsSt) {D : DegPre R} (hB : D.TauBimult) (E : Fam D (FractionRing R) 1)
    (g : ∀ α : D.X, D.SecB 1 α)
    (hg : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε 1) (E.s α) (D.famφB α)
      (DegPre.famε 1) (g α) (DegPre.prB D (FractionRing R)).left 1) : LevelOneEq D g := by
  rintro mu _ rfl T κ y z J hJ
  suffices H : ∀ β, β = 0 + 1 • mu → sval (g β) y.left z J = sval (g 0) (y * cP D T mu).left z J *
      (val (D.psi mu) (κ.left ≫ jFK (R := R) (FractionRing R)) z J * val D.rig T.hom z J).val from
    H mu (by rw [zero_add, one_smul])
  rintro _ rfl
  let ρ : T ⟶ DegPre.BF D (FractionRing R) := lift κ y
  have ρ₁ : ρ ≫ fst _ _ = κ := lift_fst _ _
  have ρ₂ : ρ ≫ DegPre.prB D (FractionRing R) = y := lift_snd _ _
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := FractionRing R) hG 1 mu 0
  have vu := hv u hu hc _ ρ z J hJ
  have hrel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (E.fe mu 0 u hu hc) _ ρ.left z J hJ
  rw [← SectionScalarValuation.secScal_sval (hg _) _ z hJ, ← SectionScalarValuation.secScal_sval (hg _) _ z hJ] at hrel
  have htr : (ρ ≫ DegPre.trF D (FractionRing R) mu) ≫ DegPre.prB D (FractionRing R) = y * cP D T mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ρ₂, comp_cP, comp_cP]
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have hu1 : uVal D (FractionRing R) 1 0 (cP D _ mu) ρ z J = 1 := by
    rw [uVal, cPoint_zero, cubN]
    simp only [Finset.prod_range_one, pow_zero, _root_.mul_one, C.face, inv_one]
  have v₃ : val D.rigK (κ.left ≫ jFK (R := R) (FractionRing R)) z J = val D.rig T.hom z J := by
    rw [← Over.w κ]
    exact (val_pull hJ _ _ _).trans (congrArg (fun q => val D.rig q z J) (Category.assoc _ _ _))
  rw [hu1, _root_.one_mul, ρ₁, LevelOneIdeal.val_famMult_one hB _ hJ, v₃] at vu
  rw [vu] at hrel
  rw [← htr, ← congrArg (fun q => sval (g (0 + 1 • mu)) q.left z J) ρ₂]
  exact hrel

theorem levelOneEq_of_expandsAt (hG : GlobalFnsSt) [IsLocalRing R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (hU : U.ExpBij 1) (σ : H0 U.LG.L 1) (f : ∀ α, D.toPre.SecB 1 α)
    (hE : ∀ e, U.ExpandsAt e 1 σ f) : LevelOneEq D.toPre f := by
  have := hR.1
  have := hR.2.2.2
  have hI : I ≤ IsLocalRing.maximalIdeal R := by
    have := IsAdicComplete.le_jacobson_bot I
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := hU.1 s
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R I hI D A G U 1 σ s
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U 1 2 ![1, -1] ![σ, σ] ![f, g]
    (fun i => by fin_cases i; exacts [hE, hg])).1 (fun j => by
      simp [Fin.sum_univ_two, scal])
  obtain rfl : f = g := funext fun α => SecOps.sec_ext fun j => by
    have := H α j
    simpa [Fin.sum_univ_two, scal, add_neg_eq_zero] using this
  exact levelOneEq_of_fam hG D.tau_bimult E f hgE

theorem LevelOneEq.eq_zero {D : DegPre R} {f : ∀ α : D.X, D.SecB 1 α} (h : LevelOneEq D f)
    [IsIntegral (DegPre.BF D (FractionRing R)).left] (z : (DegPre.BF D (FractionRing R)).left) {J}
    (hJ : Good D.P.L z J) (h0 : sval (f 0) (DegPre.prB D (FractionRing R)).left z J = 0) (mu : D.X) (j) :
    (f mu).f j = 0 := by
  have hL := D.P.isLB
  have inj := PullIntegral.prB_app_injective D (FractionRing R)
  have ext : ∀ α, (∀ y J, Good D.P.L y J → sval (f α) (DegPre.prB D (FractionRing R)).left y J = 0) →
      ∀ j, (f α).f j = 0 := fun α H j =>
    PullIntegral.sec_ext_of_inj hL _ inj (s' := SecOps.secZero) (fun y J hJ => by
      rw [Category.id_comp, H y J hJ]
      exact (ThetaScalar.sval_eq_zero SecOps.secZero (fun _ => rfl) _ y hJ).symm) j
  have e₀ := ThetaScalar.eq_zero_of_germ (H1.SectionArithmetic.pullSec (f 0) (DegPre.prB D (FractionRing R)).left) z hJ
    (by rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.id_comp, h0])
  have e₁ : ∀ j, (f 0).f j = 0 := ext 0 fun y J hJ => by
    have := ThetaScalar.sval_eq_zero _ e₀ (𝟙 _) y hJ
    rwa [H1.SectionArithmetic.sval_pullSec _ _ _ y hJ, Category.id_comp] at this
  refine ext mu (fun y J hJ => ?_) j
  rw [h mu 0 rfl _ (fst _ _) _ y J hJ, ThetaScalar.sval_eq_zero _ e₁ _ y hJ, MulZeroClass.zero_mul]

theorem prod_famB (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (y : T ⟶ D.P.A) (α : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (y.left ≫ D.famφB α i) ^ DegPre.famε 1 i =
      h (y * cP D T α).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have a₁ : y.left ≫ D.famφB α 1 = (y * cP D T α).left := congrArg (fun z => z.left)
    ((MonObj.comp_mul y (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : y.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun z => z.left) (comp_cP D y α)
  have a₃ : y.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) y)
  rw [Fin.prod_univ_four, a₁, a₂, a₃]
  show _ ^ (((1 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  simp

theorem cP_comp {D D' : DegPre R} (Φ : D'.P.A ⟶ D.P.A) {x : D'.X} {x' : D.X} (hc : D'.c x ≫ Φ = D.c x')
    (T : Over (Spec (CommRingCat.of R))) : cP D' T x ≫ Φ = cP D T x' := by
  rw [cP, Category.assoc, hc, cP]

theorem famφB_comp {D D' : DegPre R} (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] {x : D'.X} {x' : D.X}
    (hc : D'.c x ≫ Φ = D.c x') (κ : Fin 4) : D'.famφB x κ ≫ Φ.left = Φ.left ≫ D.famφB x' κ := by
  fin_cases κ
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · refine congrArg (fun q : D'.P.A ⟶ D.P.A => q.left)
      (show (𝟙 _ * cP D' _ x) ≫ Φ = Φ ≫ (𝟙 _ * cP D _ x') from ?_)
    rw [MonObj.mul_comp, MonObj.comp_mul, cP_comp Φ hc, comp_cP, Category.id_comp, Category.comp_id]
  · refine congrArg (fun q : D'.P.A ⟶ D.P.A => q.left) (show cP D' _ x ≫ Φ = Φ ≫ cP D _ x' from ?_)
    rw [cP_comp Φ hc, comp_cP]
  · refine congrArg (fun q : D'.P.A ⟶ D.P.A => q.left) (show 1 ≫ Φ = Φ ≫ 1 from ?_)
    rw [MonObj.one_comp, MonObj.comp_one]

theorem zF_fst (D : DegPre R) : (DegPre.zF D (FractionRing R)).left ≫
    (fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R) = 𝟙 (TK R).left := by
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : jFK (R := R) (FractionRing R) = 𝟙 (TK R).left := Spec.map_id _
  rw [← Category.assoc, ← Over.comp_left, z₁, Over.id_left, z₂]
  exact Category.comp_id _

theorem unit_cancel {A : Type} [CommRing A] [IsDomain A] {a b c p p' q : Aˣ} {s : A} (hs : s ≠ 0)
    (h : (a * b⁻¹ * c).val * (s * (p' * q).val) = a.val * s * (p * (c * q)).val) : p = b⁻¹ * p' := by
  have e : a * b⁻¹ * c * (p' * q) = a * (p * (c * q)) := Units.ext (mul_left_cancel₀ hs (by
    simp only [Units.val_mul] at h ⊢
    linear_combination h))
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'

theorem psi_maps {D D' : DegPre R} (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] (w : LB.Iso D'.P.L (D.P.L.pull Φ.left))
    (hw : w.IsGen)
    (hrig : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (𝟙 _))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, D'.c x ≫ Φ = D.c (xe x)) (f : ∀ α, D.SecB 1 α) (f' : ∀ α, D'.SecB 1 α)
    (hf : ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J) (J'), Good D.P.L z J → Good D'.P.L z J' →
      sval (f (xe x)) (r ≫ Φ.left) z J =
        (∏ κ, ExpTrans.om w z J J' (r ≫ D'.famφB x κ) ^ DegPre.famε 1 κ).val * sval (f' x) r z J')
    (h : LevelOneEq D f) (h' : LevelOneEq D' f') (hne : ¬ ∀ mu j, (f' mu).f j = 0) (x : D'.X) :
    PMaps w (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x) (D.psi (xe x)) (𝟙 _) := by
  have hL := D.P.isLB
  have hL' := D'.P.isLB
  have pg := (isGen_iff w).1 hw
  have := D'.P.isAb.smooth
  have := D'.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D' (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D'.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D'.P.A.hom).flip
  have hx : D'.xK x ≫ Φ.left = D.xK (xe x) := congrArg (fun q => q.left) (cP_comp Φ (hc x) (TK R))
  let T := DegPre.BF D' (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let π : T.left ⟶ (TK R).left := κ.left ≫ jFK (R := R) (FractionRing R)
  have key : ∀ (z : T.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) π z J = (ExpTrans.om w z J J' (π ≫ D'.xK x))⁻¹ * val (D'.psi x) π z J' := by
    intro z J J' hJ hJ'
    let y : T ⟶ D'.P.A := DegPre.prB D' (FractionRing R) * (cP D' T x)⁻¹
    have hy : y * cP D' T x = DegPre.prB D' (FractionRing R) := inv_mul_cancel_right _ _
    have hyΦ : (y ≫ Φ) * cP D T (xe x) = DegPre.prB D' (FractionRing R) ≫ Φ := by
      rw [← cP_comp Φ (hc x), ← MonObj.mul_comp, hy]
    have e₁ := h (xe x) (xe 0) (map_zero xe) T κ (y ≫ Φ) z J hJ
    have e₂ := h' x 0 rfl T κ y z J' hJ'
    have e₃ := hf x _ y.left z J J' hJ hJ'
    have e₄ := hf 0 _ (DegPre.prB D' (FractionRing R)).left z J J' hJ hJ'
    rw [prod_famB, hy] at e₃
    rw [prod_famB, cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at e₄
    rw [hy] at e₂
    rw [hyΦ] at e₁
    have e₅ : val D.rig T.hom z J = ExpTrans.om w z J J' (1 : T ⟶ D'.P.A).left * val D'.rig T.hom z J' := by
      have o' : T.hom ≫ eSec D'.P.A = (1 : T ⟶ D'.P.A).left := rfl
      have o : (T.hom ≫ eSec D'.P.A) ≫ Φ.left = T.hom ≫ eSec D.P.A :=
        congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.one_comp Φ)
      have := hrig _ T.hom z (fun _ => J ((T.hom ≫ eSec D'.P.A) ≫ Φ.left)) (fun _ => J' (T.hom ≫ eSec D'.P.A))
        (fun _ => hJ ((T.hom ≫ eSec D'.P.A) ≫ Φ.left)) (fun _ => hJ' (T.hom ≫ eSec D'.P.A))
      rw [Fintype.prod_unique, zpow_one] at this
      refine Eq.trans ?_ this
      refine (val_of D.rig T.hom z J (fun _ => J ((T.hom ≫ eSec D'.P.A) ≫ Φ.left)) fun _ => congrArg J o.symm).trans ?_
      exact congrArg (fun q => gm q z _ _) (Category.comp_id _).symm
    have e₆ : π ≫ D'.xK x = (cP D' T x).left := by
      let k : T ⟶ TK R := Over.homMk π ((Category.assoc _ _ _).trans (Over.w κ))
      exact congrArg (fun q => q.left) (comp_cP D' k x)
    have ne : sval (f' 0) (DegPre.prB D' (FractionRing R)).left z J' ≠ 0 := fun e => hne (h'.eq_zero z hJ' e)
    have e₇ := e₃.symm.trans (e₁.trans (congrArg₂ (· * ·) e₄ rfl))
    rw [e₂, e₅] at e₇
    rw [e₆]
    exact unit_cancel ne e₇
  obtain ⟨t, ht, hv⟩ := exists_up pg hL hL' (φ' := fun _ : PUnit => D'.xK x) (D'.psi x) (D'.psi_gen x)
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi (xe x)) π) (LB.pullGen D.P.L _ _ t π) :=
    corr_of_val hL fun z J hJ => by
      choose J' hJ' using fun ψ : T.left ⟶ D'.P.A.left => exists_chart hL' (ψ z)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, key z J J' hJ hJ']
      refine Eq.trans ?_ (hv _ π z _ _ (Good.mem hJ _ π) (Good.mem hJ' _ π)).symm
      rw [pw, Fintype.prod_unique, zpow_neg_one, ExpTrans.om, Category.assoc]; rfl
  have hz : (DegPre.zF D' (FractionRing R)).left ≫ π = 𝟙 (TK R).left := by
    exact zF_fst D'
  refine RigidIsoCube.pmaps_of_section pg hL hL' _ (D'.psi_gen x) _ (D.psi_gen _) (fun _ => hx) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id) fun y J J' hJ hJ' => ?_
  have := val_corr hJ hcorr (DegPre.zF D' (FractionRing R)).left
  rw [val_pull hJ, val_pull hJ, hz] at this
  refine this.trans ((hv _ (𝟙 _) y _ _ (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [pw, Fintype.prod_unique, Fintype.prod_unique, Category.assoc]

end GlobalTheory.PsiCompare

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare in

theorem unifPre_psi_correspond : GlobalFnsSt → SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → U.ExpBij 1 → U'.ExpBij 1 → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, ((∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∀ e : ℕ, ((U'.gt e).pG.left ≫ Φ.hom.left = (𝟙 _) ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ Φ.hom.left = (𝟙 _) ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (xe x)) (𝟙 _))) → ∀ x, Geo.Tor.PMaps w (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1) (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _) := by
  intro hG hS R _ _ _ I hR D D' A A' G _ _ hsa U U' wL _ hwL _ hU hU' Φ w ⟨hw, hlev⟩ ⟨hΦ, hrig⟩ xe ⟨hc, ht⟩
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  obtain ⟨b, -, hb⟩ := GenericSectionBasis.exists_secK_basis hS R I D A G U 1 le_rfl
  let i₀ : Fin (1 ^ A.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have hs : ¬ ∀ j, (b i₀).f j = 0 := fun h0 => by
    obtain ⟨c, -, hc⟩ := hb SecOps.secZero
    have e₁ := hc 0 (fun j => by simp [scal]; rfl)
    have e₂ := hc 1 (fun j => by
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      obtain rfl : i = i₀ := Fin.ext (by have := i.2; simp only [one_pow] at this; show i.1 = 0; omega)
      rw [h0 j, MulZeroClass.mul_zero])
    exact one_ne_zero (congrFun (e₂.trans e₁.symm) i₀)
  obtain ⟨E, ⟨r, hr, σ, f, hσ, -, hE⟩, -⟩ := hU.1 (b i₀)
  have hφ := fun x => famφB_comp Φ.hom (hc x)
  obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ _ U.LG.isLB U'.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 G.left) (fun _ => rfl) σ
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw (Fin 4)
    (D'.toPre.famφB x) (D.toPre.famφB (xe x)) (DegPre.famε 1) Φ.hom.left (hφ x) (f (xe x))).exists
  have hE' : ∀ e, U'.ExpandsAt e 1 σ' f' := fun e =>
    expandsAt_transport R R I I D D' A A' G G U U' Φ.hom.left w xe (𝟙 _) wL hw hwL hφ e e 1 (𝟙 _)
      ⟨(Category.id_comp _).trans (Category.comp_id _).symm, ht e, fun Z ρ z jM jM' jL jL' h₁ h₂ h₃ h₄ => by
        rw [Category.comp_id]
        exact (hlev e).2 Z ρ z jM jM' jL jL'
          ((congrArg (fun q => q (ρ z) ∈ D.toPre.P.L.U jM) (hlev e).1).mp h₁) h₂ h₃ h₄⟩ σ σ' f f' hσ' hf' (hE e)
  refine psi_maps Φ.hom w hw hrig xe hc f f' (fun x Z ρ z J J' hJ hJ' =>
      ExpTrans.sec_val w _ _ _ Φ.hom.left (hφ x) (f (xe x)) (f' x) ρ z (hf' x _ ρ z) hJ hJ')
    (levelOneEq_of_expandsAt hG hR U hU σ f hE) (levelOneEq_of_expandsAt hG hR U' hU' σ' f' hE') fun h0 => hs ?_
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D' A' G U' 1 1 ![1] ![σ'] ![f']
    (fun i => by fin_cases i; exact hE')).2 hsa.geomConnected (fun α j => by
      simpa [scal] using h0 α j)
  have H' : ∀ j, σ'.f j = 0 := fun j => by simpa [scal] using H j
  refine ThetaScalar.eq_zero_of_sval U.LG.isLB _ fun y J hJ => ?_
  choose J' hJ' using fun ψ : pullback G.hom (jK R) ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
  have e₁ := PullIntegral.sval_of_secScal hσ (𝟙 _) y hJ
  have e₂ := ExpTrans.sec_val wL _ _ _ (𝟙 G.left) (fun _ => rfl) σ σ' (𝟙 _ ≫ pullback.fst G.hom (jK R)) y
    (hσ' _ _ y) hJ hJ'
  rw [ThetaScalar.sval_eq_zero σ' H' _ y hJ', MulZeroClass.mul_zero, Category.comp_id, e₁] at e₂
  have e₃ : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK R) ≫ jK R) r) =
      cst (pullback.snd G.hom (jK R) ≫ jK R) y r :=
    (gs_pull (𝟙 _) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  rw [e₃] at e₂
  exact (IntegralExpansionLocal.isUnit_cst_of_ne_zero _ y hr).mul_right_eq_zero.1 e₂

end GlobalTheory
