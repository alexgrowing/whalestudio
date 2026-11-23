import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpanEqTopOfCard

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionImage

open FieldBaseChange

theorem translT_translPt {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (y * x) := by
  show lift (fst T A) ((fst T A ≫ x) * snd T A) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, _root_.mul_assoc]

theorem translPt_one {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_inv {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) :
    translT A x⁻¹ ≫ translT A x = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((translT_translPt _ _).trans (by rw [mul_inv_cancel, translPt_one]))

theorem eq_of_gen {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F] (q : Spec (CommRingCat.of F) ⟶ S)
    (x x' : Over.mk q ⟶ P.A)
    (r : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(translPt P.A x).left, (translPt P.A x').left] ![1, -1]))
    (hr : r.IsGen) : x = x' := by
  refine mul_inv_eq_one.1 (P.ktriv F q (x * x'⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  obtain ⟨w, hw, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(translPt P.A (x * x'⁻¹)).left, (snd (Over.mk q) P.A).left]) r hr (translT P.A x'⁻¹).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (translT_translPt x'⁻¹ x)
      · exact congrArg (fun q => q.left) ((translT_translPt x'⁻¹ x').trans
          (by rw [mul_inv_cancel, translPt_one])))
  exact exists_isGen_pull (translDiff P.A P.L (x * x'⁻¹)) w hw _

theorem exists_smul_of_phiVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ s t t' : Fam D F k, DVR.PhiVal p w s.s t.s → DVR.PhiVal p w' s.s t'.s → t' = c • t := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw' (DVR.invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (DVR.prod_sum₂ _ (c := ∏ i, h (DegPre.lineφ D F p.g.b i) ^ DegPre.lineε k i) rfl
        (DVR.prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun s t t' h h' => DVR.phi_unique p w' h' fun α β e' T ρ z J hJ => ?_⟩
  · rintro rfl
    let z : (TF (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (𝟙 _) z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · have e := ha _ (ρ ≫ fst _ _).left z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine (DVR.sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β e' T ρ z J hJ, val_mul hJ, val_mul hJ]
    refine (congrArg (· * _) e.symm).trans ?_
    rw [mul_left_comm, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem pt_eq_of_proportional (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) {n : ℕ} (hn : 1 ≤ n)
    (θ θ' : ThetaGrp P.A P.L (n : ℤ) (Over.mk q)) (c : Γ((Over.mk q).left, ⊤)ˣ)
    (H : ∀ t u u', IsActOf P.A P.L (n : ℤ) θ t u → IsActOf P.A P.L (n : ℤ) θ' t u' → ∀ y J, Good P.L y J →
      VVRank.sv P.A u' (𝟙 _) y J =
        (gm (𝟙 _ ≫ (fst (Over.mk q) P.A).left) y ⊤ c).val * VVRank.sv P.A u (𝟙 _) y J) : θ.pt = θ'.pt := by
  have hL := P.isLB
  let T := Over.mk q
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ P.A
  have : IsIntegral (T ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F _
  have hN : ∀ y : (T ⊗ P.A).left, IsIntegrallyClosed ((T ⊗ P.A).left.presheaf.stalk y) := fun y =>
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ (fst T P.A).left
      (inferInstanceAs (Smooth (pullback.fst q P.A.hom)))).2.1 y).2
  obtain ⟨b, hb, -⟩ := BoxSpan.exists_basis hS P 1 le_rfl F q
  have : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hb.ne_zero ⟨0, by simp⟩
  let th : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))) :=
    SecM.toSec P.A (b ⟨0, by simp⟩)
  have tr : ∀ x : T ⟶ P.A, ∃ s : LB.Sec (LB.LinComb P.L (K := PUnit) (fun _ => (translPt P.A x).left) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = sval th (r ≫ (translT P.A x).left) z J := fun x => by
    have e : (translT P.A x).left ≫ (snd T P.A).left = (translPt P.A x).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : translT P.A x ≫ snd T P.A = _)
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : PUnit => (translPt P.A x).left) (ε' := fun _ => 1)
      (fun U _ h => by simp only [e, Fintype.prod_unique, Nat.cast_one]) (H1.SectionArithmetic.pullSec th (translT P.A x).left)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  obtain ⟨s, hs⟩ := tr θ.pt
  obtain ⟨s', hs'⟩ := tr θ'.pt
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T P.A).left) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (H1.SectionArithmetic.powSec fun _ : Fin n => th)
  have ht' : ∀ (r : (T ⊗ P.A).left ⟶ (T ⊗ P.A).left) y J, Good P.L y J → sval t r y J = sval th r y J ^ n :=
    fun r y J hJ => by
      rw [ht _ r y J hJ, H1.SectionArithmetic.sval_powSec _ r y hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ t u := VVRank.exists_isTwistPull P.A hL θ.isGen t
  obtain ⟨u', hu'⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ' t u := VVRank.exists_isTwistPull P.A hL θ'.isGen t
  have hc : (constGen P.A P.L c).IsGen := isGen_of_gm _ fun y j j' _ _ => by
    obtain rfl : j = j' := Subsingleton.elim _ _
    rw [trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨v, hv, hv'⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(translPt P.A θ'.pt).left, (translPt P.A θ.pt).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (LB.mulGen P.L _ _ _ _ (LB.invGen P.L ![(snd T P.A).left, (translPt P.A θ'.pt).left] ![(n : ℤ), -(n : ℤ)] θ'.φ)
      (LB.mulGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n : ℤ), -(n : ℤ)] _ _ θ.φ
        (constGen P.A P.L c)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ'.isGen)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN P.L hL _ _ n hn s' s v hv (by
    by_contra h0
    have h0' : ∀ j, s.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    refine hne (Subtype.ext (funext fun j => sec_ext_val (s := th) (s' := H1.SectionArithmetic.secZero _) hL
      (fun y J hJ => ?_) j))
    have e := hs _ (translT P.A θ.pt⁻¹).left y J hJ
    rw [← Over.comp_left, translT_inv, Over.id_left] at e
    refine e.symm.trans (Eq.trans ?_ (gs_zero' _ y _ (hJ.mem _ _)).symm)
    exact (congrArg (gs _ y _) (h0' _)).trans (gs_zero' _ y _ (hJ.mem _ _))) (fun y J hJ => by
    have e := H t u u' hu hu' y J hJ
    rw [VVRank.sv_of_isTwistPull P.A hu _ y hJ, VVRank.sv_of_isTwistPull P.A hu' _ y hJ] at e
    have e₁ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs _ (𝟙 _) y J hJ).symm)
    have e₂ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs' _ (𝟙 _) y J hJ).symm)
    have e₃ := (congrArg _ e₂).symm.trans (e.trans (congrArg _ (congrArg _ e₁)))
    have e₄ := (hv' _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (H1.val_constGen _ c _ y J)))))
    rw [e₄, Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.val_mul, _root_.mul_assoc]
    exact e₃.trans (mul_left_comm _ _ _))
  exact (eq_of_gen P q _ _ r hr).symm

theorem qkToAkU_unique : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → QkToAkU U.toUnifPre F n p x' → x = x' := by
  intro hL _ R _ _ I _ D A G _ _ _ U F _ _ n hn p x x' hx hx'
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

end GlobalTheory.TorsionImage
