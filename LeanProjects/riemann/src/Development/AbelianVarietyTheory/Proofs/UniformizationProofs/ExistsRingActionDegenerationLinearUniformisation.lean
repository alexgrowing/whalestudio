import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinearStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommuteStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CorrOfGenericOfIsSeparated

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.RingActData

variable {R : Type} [CommRing R] [IsDomain R]

theorem corr_of_val_field (F : Type) [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TK R).left ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ (y : (TF (R := R) F).left) J, Good L y J →
      val t (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J = val t' (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hf : Flat (jFK (R := R) F) := Flat.SpecMap_iff.2 (by
    show (algebraMap (FractionRing R) F).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have hs : Surjective (jFK (R := R) F) := ⟨fun x => ⟨(⊥ : PrimeSpectrum F),
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _⟩⟩
  have he : Epi (jFK (R := R) F) := Flat.epi_of_flat_of_surjective _
  refine GlobalTheory.corr_of_corr_pullGen L φ ε φ' ε' t t' (jFK (R := R) F) (fun U => GlobalTheory.FunDescent.app_injective _ U)
    (fun a b e => (cancel_epi _).1 e) (corr_of_val hL fun y J hJ => ?_)
  exact (val_pull hJ _ _ _).trans ((h y J hJ).trans (val_pull hJ _ _ _).symm)

theorem prod_O (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ b χ i) ^ Oε i =
      h (cP D _ χ * b).left * (h (cP D _ χ).left)⁻¹ * (h b.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, mul_comm (cP D _ χ) b]
  show h (b * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h b.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oinv (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ b χ i) ^ Oinvε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, mul_comm (cP D _ χ) b]
  show h (b * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem val_eq_rosati (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (χ χ' : D.X) (hc : D.c χ' = D.c χ ≫ f)
    (v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) χ') (D.Oφ g χ)) (Sum.elim Oε Oinvε))) (hv : Normd v)
    {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val v x.left z J = val₂ u z J (cP D T χ) x := by
  have cf : ∀ T, cP D T χ' = cP D T χ ≫ f := fun T => by rw [cP, hc, ← Category.assoc]; rfl
  have vp : ∀ {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) (𝟙 D.P.A)).left) x.left z J = val₂ u z J (cP D T χ) x :=
    fun x z J hJ => by
      rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]; rfl
  refine Eq.trans (gen_unique' D.P.isLB (fun U _ h => ?_) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    hv.1 (pullGen_isGen _ _ _ _ hu _) (fun y I hI => ?_) _ x.left z J hJ) (vp x z J hJ)
  · refine (prod_ros f g (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.trans ?_
      (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_O D (𝟙 _) χ' h) (prod_Oinv D g χ h)).symm)
    rw [cf, Category.id_comp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have a₁ := val_corr hI hv.2 (𝟙 _)
    rw [val_pull hI, Category.id_comp, val_one] at a₁
    have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
    have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ _) hI 1 1 (cP D _ χ)).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = η[D.P.A] := by simp [Hom.one_def]
    have e₂ := mul_eq_left.1 e.symm
    rw [e₁] at e₂
    exact a₁.trans (e₂.symm.trans (vp η[D.P.A] y I hI).symm)

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem tauBal_of_act (hG : GlobalFnsSt) {U : UnifPre I D A G} (E E' : EndU U) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (hc : ∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB)
    (hex : ∀ g : GtPtF D.toPre F, ∃ g', E.Act g g')
    (hb : ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') :
    D.toPre.TauBal E'.aB E.aB E.h E'.h := by
  intro u hu u₀ χ y
  have := E.homB
  have := E'.homB
  refine corr_of_val_field F D.toPre.P.isLB fun z J hJ => ?_
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
  obtain ⟨g', hg'⟩ := hex g
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hg
  obtain ⟨-, ιv'⟩ := (isIota_iff _ _).1 (hb y g g' hg hg')
  have e := hg'.2 χ z J hJ
  rw [ιv' χ z J hJ, ιv _ z J hJ, val_eq_rosati hG D.toPre E'.aB E.aB u hu u₀ χ _ (hc χ) (E.u χ) (E.u_norm χ) g.b z J hJ,
    ιb] at e
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
    rw [Category.id_comp]; rfl)
  have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
      val₂ u z J (cP D.toPre _ χ) (cP D.toPre _ y) := by
    rw [val_pull hJ, val₂, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
  refine (val_mul hJ _ _ _).trans ?_
  exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) e').trans
    (e.symm.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

theorem exists_oAct : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] (ιA : A.OAct O) (ιG : RingAct G O), (∀ a, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a) → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∃ (_ : Module O D.toPre.X) (ιD : D.toPre.OAct O), U.toUnifPre.OLinear O ιD ιA ιG := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hI D A G _ _ hS U O _ _ ιA ιG hext hros
  choose E EG EA using fun a => GlobalTheory.T.exists_endomorphism_action_uniformization_data hL R I hI D A G hS U (ιG.act a) (ιA.act a) (ιG.hom a) (ιA.hom a) (hext a)
  have hcalc := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hS U (AlgebraicClosure (FractionRing R))
  have hadj : ∀ a, LBIso (cubeLB G ![fst G G ≫ (E a).aG, snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (E (star a)).aG] U.LG.L) := fun a => by
    rw [EG, EG]; exact hros a
  have ros := fun a => GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL R I hI D A G hS U _ _ (hadj a)
  have bal := fun a => (GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL h₁ h₂ h₃ h₄ R I hI D A G hS U (AlgebraicClosure (FractionRing R)) _ _ (hadj a)).1
  obtain ⟨E₁, g₁, -, b₁, x₁, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hI D A G hS U).1 1
  have one := (hcalc (E 1) E₁ E₁).2.2.2.1 (by rw [EG, ιG.map_one, g₁, pow_one])
  have add := fun a b => (hcalc (E a) (E b) (E (a + b))).2.2.2.2.1 (by rw [EG, EG, EG, ιG.map_add]; rfl)
  have mul := fun a b => (hcalc (E b) (E a) (E (a * b))).2.2.2.2.2 (by rw [EG, EG, EG, ιG.map_mul])
  let M : Module O D.toPre.X :=
    { smul := fun a y => (E (star a)).h y
      one_smul := fun y => by
        show (E (star 1)).h y = y
        rw [star_one, one.2.1, x₁, one_nsmul]
      mul_smul := fun a b y => by
        show (E (star (a * b))).h y = (E (star a)).h ((E (star b)).h y)
        rw [star_mul, (mul _ _).2.1]; rfl
      smul_zero := fun a => map_zero (E (star a)).h
      smul_add := fun a => map_add (E (star a)).h
      add_smul := fun a b y => by
        show (E (star (a + b))).h y = (E (star a)).h y + (E (star b)).h y
        rw [star_add, (add _ _).2.1]; rfl
      zero_smul := fun y => by
        show (E (star 0)).h y = 0
        have := DFunLike.congr_fun (add 0 0).2.1 y
        rw [add_zero, AddMonoidHom.add_apply] at this
        rw [star_zero]
        exact left_eq_add.1 this }
  have sm : ∀ a, (fun y : D.toPre.X => star a • y) = (E a).h := fun a => funext fun y => by
    show (E (star (star a))).h y = _
    rw [star_star]
  refine ⟨M,
    { onB :=
        { act := fun a => (E a).aB
          hom := fun a => (E a).homB
          map_one := by rw [one.1, b₁, pow_one]
          map_mul := fun a b => (mul a b).1
          map_add := fun a b => (add a b).1
          rosati := fun a => (ros a).2.1 }
      c_lin := fun a y => (ros a).2.2.2 y
      tau_bal := fun a => ?_ }, hext, fun e a => ?_, fun e a => ?_⟩
  · have hb := bal (star a)
    rw [star_star] at hb
    rw [sm]
    exact tauBal_of_act hL.1.globalFns (E (star a)) (E a) _ (ros a).2.2.2
      (fun g => ((hcalc (E (star a)) E₁ E₁).1 g).exists) hb
  · rw [← EG]; exact (E a).q_lin e
  · rw [← EG, sm]; exact (E a).i_lin e

end GlobalTheory.RingActData
