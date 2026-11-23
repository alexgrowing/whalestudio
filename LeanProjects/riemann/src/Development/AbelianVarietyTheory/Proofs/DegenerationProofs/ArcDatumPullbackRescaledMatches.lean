import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPsiOnBasicOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.RescaleMatch

theorem genRel_rescale {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg f D D') (q : D'.X → (FractionRing R')ˣ) (F : Type) [Field F]
    [Algebra (FractionRing R') F] [Algebra (FractionRing R) F]
    (hF : ∀ x, algebraMap (FractionRing R) F (algebraMap R _ x) = algebraMap (FractionRing R') F (algebraMap R' _ (f x)))
    (x : D'.X) :
    GenRel hD.w (LB.pullGen _ _ _ ((TauTwist.rescale D' q).psi x) (jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi (hD.xe x)) (jFK (R := R) F)) (algebraMap (FractionRing R') F (q x)) := by
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap f = jFK (R := R) F ≫ jK R :=
    (congrArg (_ ≫ ·) (Geo.Tor.spMap_comp f _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext fun x => (hF x).symm)).trans (Geo.Tor.spMap_comp _ _)))
  have hx : D'.xK x ≫ PsiEvenPull.proj hD = jK R' ≫ specOf f ≫ (D.c (hD.xe x)).left := by
    rw [← hD.c_pr x, ← Category.assoc]; rfl
  have hpt : (jFK (R := R') F ≫ D'.xK x) ≫ PsiEvenPull.proj hD = jFK (R := R) F ≫ D.xK (hD.xe x) := by
    rw [Category.assoc, hx, ← Category.assoc (jK R'), ← Category.assoc]
    exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
  have z : Sp F := (default : PrimeSpectrum F)
  refine (ArcPsiOn.genRel_iff_val D'.P.isLB D.P.isLB hD.w _ _ _ z).2 ⟨hpt, fun J J' hJ hJ' => ?_⟩
  have e := ArcPull.psi_val hD (jFK (R := R) F) (jFK (R := R') F) hj hJ hJ' x
  have e₁ := TauTwist.val_psi_rescale q x (jFK (R := R') F) hJ'
  have e₂ := TauTwist.unitAt_spMap (𝟙 (Sp F)) (algebraMap (FractionRing R') F) z (q x)
  rw [Category.id_comp] at e₂
  have e₃ : (TauTwist.unitAt (𝟙 (Sp F)) z (Units.map (algebraMap (FractionRing R') F).toMonoidHom (q x))).val =
      toStk z (algebraMap (FractionRing R') F (q x)) := gm_val _ z ⊤ trivial _
  rw [zpow_neg_one, ← e₃, ← Units.val_mul]
  exact congrArg Units.val ((congrArg₂ (· * ·) rfl (((val_pull hJ' _ _ _).trans (by rw [Category.id_comp])).trans e₁)).trans
    ((mul_left_comm _ _ _).trans (congrArg₂ (· * ·) e₂
      (e.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm))))

theorem exists_match_rescale : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] (f : O' →+* R) (D' : DegPre R) (hD : IsPullDeg f a.D₀ D') (u₀ : R) (uK : (FractionRing R)ˣ), (uK : FractionRing R) = algebraMap R _ u₀ → ∀ (q : D'.X → (FractionRing R)ˣ) (Φ : D'.P.A.left ⟶ a.D₀.P.A.left), Φ = PsiEvenPull.proj hD → (∀ y, q y = uK ^ (a.be (hD.xe y) (hD.xe y) / 2)) → ∃ (_ : Module (𝓞 E) (TauTwist.rescale D' q).X) (oW : letI := H.starRing; (TauTwist.rescale D' q).OAct (𝓞 E)) (he : _) (w : _) (e : _), GlobalTheory.LN.Match a f u₀ (TauTwist.rescale D' q) oW Φ he w e ∧ (∀ y, hD.xe (e y) = y) ∧ (TauTwist.rescale D' q).PsiEven ∧ (TauTwist.rescale D' q).TauBimult := by
  intro hG E _ _ _ H D l c O _ β O' _ _ b a R _ _ f D' hD u₀ uK hu q Φ hΦ hq
  subst hΦ
  letI := H.starRing
  obtain ⟨inst, o', hs, ho⟩ := exists_oAct_of_isPullDeg hG O' R f a.D₀ D' hD (𝓞 E) a.oa
  have hw := TauTwist.halfUnit_add_star H
  have ht : TauTwist.IsScalarForm (𝓞 E) fun y x : D'.X => uK ^ a.be (hD.xe y) (hD.xe x) :=
    ⟨fun y x x' => by rw [map_add, map_add, zpow_add], fun y x => by rw [a.be_symm],
      fun r y x => by rw [hs, hs, a.be_adj]; rfl⟩
  obtain rfl : q = fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y)) := funext fun y => by
    have h₁ : a.be (hD.xe y) (H.bar H.w0 • hD.xe y) = a.be (hD.xe y) (H.w0 • hD.xe y) := by
      rw [← a.be_adj, a.be_symm]
    have h₂ : a.be (hD.xe y) ((H.w0 + H.bar H.w0) • hD.xe y) = a.be (hD.xe y) (hD.xe y) := by
      rw [show H.w0 + H.bar H.w0 = 1 from hw, one_smul]
    rw [add_smul, map_add, h₁] at h₂
    rw [hq, hs, ← h₂]
    congr 1
    omega
  let e : D'.X ≃ₗ[𝓞 E] a.D₀.X := { hD.xe with map_smul' := hs }
  have he : ∀ y, hD.xe (e.symm y) = y := fun y => e.apply_symm_apply y
  let oW : (TauTwist.rescale D' fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y))).OAct (𝓞 E) :=
    (TauTwist.twistAct (D := D') hw ht o' :)
  have ev := TauTwist.psiEven_twist (D := D') ht H.w0 (PsiEvenPull.psiEven_pull hG _ _ f _ _ hD a.even)
  have bi := TauTwist.tauBimult_twist (D := D') hw ht (tauBimult_of_isPullDeg hG _ _ f _ _ hD a.bimult)
  refine ⟨inst, oW, hD.he, hD.w, e.symm,
    ⟨pull_grp hD, hD.w_gen, hD.w_rig, fun x => ?_, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩, he, ev, bi⟩
  · have e₀ := congrArg (fun z => z.left ≫ pullback.fst a.D₀.P.A.hom (specOf f)) (ho x)
    have e₂ : ((Over.pullback (specOf f)).map (a.oa.onB.act x)).left ≫
        pullback.fst a.D₀.P.A.hom (specOf f) = pullback.fst _ _ ≫ (a.oa.onB.act x).left :=
      pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc, e₂] at e₀
    exact e₀.trans (Category.assoc _ _ _).symm
  · exact (hD.c_pr (e.symm y)).trans (by rw [he])
  · have k := genRel_rescale hD (fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y))) F hF (e.symm y)
    have v : algebraMap (FractionRing R) F ((uK ^ a.be (hD.xe (e.symm y)) (hD.xe (H.w0 • e.symm y)) : (FractionRing R)ˣ) :
        FractionRing R) = uF ^ (a.be y y / 2) := by
      rw [show uK ^ a.be (hD.xe (e.symm y)) (hD.xe (H.w0 • e.symm y)) = _ from hq (e.symm y), he,
        Units.val_zpow_eq_zpow_val, map_zpow₀, hu, huF]
    beta_reduce at k
    rw [v, he] at k
    exact k

end GlobalTheory.RescaleMatch
