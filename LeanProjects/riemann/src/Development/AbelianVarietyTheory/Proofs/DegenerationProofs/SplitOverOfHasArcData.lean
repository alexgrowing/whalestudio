import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsSemiAbelianIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcSplit

open CoordToExt TorusCoord

section Unique

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem exists_coordHom (g : GtCoord I D e G) (g' : GtCoord I D e G') :
    ∃ F : thickObj R I e G ⟶ thickObj R I e G', F.left ≫ g'.pG.left = g.pG.left ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
        val (g'.t χ) (r ≫ F.left) z J = val (g.t χ) r z J := by
  obtain ⟨F, hF⟩ := (toGtPt_bijective g' (T := thickObj R I e G)).2 (toGtPt g (𝟙 _))
  have h := isPointOf_toGtPt g (𝟙 (thickObj R I e G))
  have h' := (toGtPt_eq_iff g' F _).1 hF
  refine ⟨F, h'.1.symm.trans (h.1.trans (Category.id_comp _)), fun χ Z r z J hJ => ?_⟩
  refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h'.2 χ) r).symm.trans
    ((val_corr hJ (h.2 χ) r).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun x => val (g.t χ) x z J) (Category.comp_id r)

theorem exists_iso_of_coord (hG : GlobalFnsSt) (g : GtCoord I D e G) (g' : GtCoord I D e G') :
    ∃ F : thickObj R I e G ≅ thickObj R I e G', IsMonHom F.hom := by
  obtain ⟨F, hF, vF⟩ := exists_coordHom g g'
  obtain ⟨F', hF', vF'⟩ := exists_coordHom g' g
  have him : ∀ {T} (x : T ⟶ thickObj R I e G), im g' (x ≫ F) = im g x := fun x =>
    Over.OverMorphism.ext ((Category.assoc x.left F.left _).trans (congrArg (x.left ≫ ·) hF))
  have mul : ∀ (T) (x y : T ⟶ thickObj R I e G), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro T x y
    refine Over.OverMorphism.ext (ext_of_val g' _ _ ?_ fun χ z J hJ => ?_)
    · have : im g' ((x * y) ≫ F) = im g' ((x ≫ F) * (y ≫ F)) := by
        rw [him, im_mul, im_mul, him, him]
      exact congrArg (·.left) this
    · have a := val_t_mul_points g hG χ x y z J hJ
      have a' := val_t_mul_points g' hG χ (x ≫ F) (y ≫ F) z J hJ
      have c : cubeVal g' χ z J (x ≫ F) (y ≫ F) = cubeVal g χ z J x y := by
        unfold cubeVal
        rw [him, him]
      rw [c] at a'
      refine (vF χ _ _ z J hJ).trans (mul_right_cancel (a.trans (Eq.trans ?_ a'.symm)))
      exact congrArg₂ (· * ·) (vF χ _ _ z J hJ).symm (vF χ _ _ z J hJ).symm
  refine ⟨⟨F, F', Over.OverMorphism.ext (ext_of_val g _ _ ?_ fun χ z J hJ => ?_),
    Over.OverMorphism.ext (ext_of_val g' _ _ ?_ fun χ z J hJ => ?_)⟩, ⟨?_, ?_⟩⟩
  · rw [Over.comp_left, Category.assoc, hF', hF]
    exact (Category.id_comp _).symm
  · refine (vF' χ _ _ z J hJ).trans (Eq.trans ?_ (vF χ _ _ z J hJ))
    exact congrArg (fun x => val (g'.t χ) x z J) (Category.id_comp _).symm
  · rw [Over.comp_left, Category.assoc, hF, hF']
    exact (Category.id_comp _).symm
  · refine (vF χ _ _ z J hJ).trans (Eq.trans ?_ (vF' χ _ _ z J hJ))
    exact congrArg (fun x => val (g.t χ) x z J) (Category.id_comp _).symm
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ _ ⟶ thickObj R I e G) ≫ F = 1 := mul_eq_left.1 h.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h'
  · have h := mul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end Unique

section Datum

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev bundle₀ (χ : D.X) : LB D.P.A.left := LB.LinComb D.P.L (D.Oφ (𝟙 D.P.A) χ) Oε

theorem comp_Oφ_id {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem bundle₀_add (χ χ' : D.X) :
    ∃ t : LB.Iso (bundle₀ D χ') (LB.div (bundle₀ D (χ + χ')) (bundle₀ D χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (𝟙 D.P.A))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (𝟙 D.P.A) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (𝟙 _) _ h) (congrArg (·⁻¹) (prod_O D (𝟙 _) _ h)))
    (congrArg (·⁻¹) (prod_O D (𝟙 _) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem bundle₀_zero : ∃ t : LB.Gen (bundle₀ D 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (𝟙 _) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem bundle₀_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ D.P.A (bundle₀ D χ)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (x2 D.P.A 0) (x2 D.P.A 1))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (x2 D.P.A 0) (x2 D.P.A 1) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, comp_Oφ_id]
  refine (prod_square (x2 D.P.A) (fun x => ∏ k, h (D.Oφ x χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D _ _ h) (congrArg (·⁻¹) (prod_O D _ _ h)))
    (congrArg (·⁻¹) (prod_O D _ _ h))) (prod_O D _ _ h)).trans ?_
  rw [_root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem bundle₀_rig (χ : D.X) : ∃ t : LB.Gen ((bundle₀ D χ).pull (eSec D.P.A)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ?_)
  have e₁ : η[D.P.A] = (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have e₂ : ∀ k, eSec D.P.A ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) χ k :=
    fun k => e₁ ▸ comp_Oφ_id D η[D.P.A] χ k
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  simp only [_root_.mul_one, e₂]
  refine (prod_O D _ _ h).trans ?_
  rw [_root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

def extOf : SplitExt (Spec (CommRingCat.of R)) where
  B := D.P.A
  isAbelian := D.P.isAb
  X := D.X
  O χ := ⟨bundle₀ D χ, (bundle₀_rig D χ).choose, DVR.linComb_isLB _ D.P.isLB _ _, (bundle₀_rig D χ).choose_spec⟩
  addIso := bundle₀_add D
  zeroTriv := bundle₀_zero D
  primitive := bundle₀_primitive D

variable {D} {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
  {f : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {φ : D'.P.A.left ⟶ D.P.A.left}

theorem Oφ_push (h : IsGrpPullback D'.P.A D.P.A f φ) {y : D.X} {y' : D'.X}
    (hc : (D'.c y').left ≫ φ = f ≫ (D.c y).left) (k : Fin 4) :
    D'.Oφ (𝟙 _) y' k ≫ φ = φ ≫ D.Oφ (𝟙 _) y k := by
  let ρ := pushHom h D'.P.A
  have e₁ : ρ (toUnit _ ≫ D'.c y') = toUnit _ ≫ D.c y := Over.OverMorphism.ext (by
    change (D'.P.A.hom ≫ (D'.c y').left) ≫ φ = (D'.P.A.hom ≫ f) ≫ (D.c y).left
    exact (Category.assoc _ _ _).trans ((congrArg (D'.P.A.hom ≫ ·) hc).trans (Category.assoc _ _ _).symm))
  have e₂ : (ρ (𝟙 _)).left = φ := Category.id_comp φ
  rw [← congrArg (· ≫ D.Oφ (𝟙 _) y k) e₂]
  refine Eq.trans ?_ (comp_Oφ_id D (ρ (𝟙 _)) y k).symm
  fin_cases k
  · exact congrArg (·.left) ((map_mul ρ (𝟙 _) (toUnit _ ≫ D'.c y')).trans (congrArg (ρ (𝟙 _) * ·) e₁))
  · exact congrArg (·.left) e₁
  · rfl
  · exact congrArg (·.left) (map_one ρ)

theorem nonempty_coord_pullback (hG : GlobalFnsSt) (h : IsGrpPullback D'.P.A D.P.A f φ)
    (w : LB.Iso D'.P.L (D.P.L.pull φ)) (hw : w.IsGen) (xe : D'.X ≃+ D.X)
    (hc : ∀ y, (D'.c y).left ≫ φ = f ≫ (D.c (xe y)).left) (I : Ideal R') (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (hE : (extOf D).IsGt G) :
    Nonempty (GtCoord I D' e ((Over.pullback f).obj G)) := by
  obtain ⟨d⟩ := hE
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (thick R' I e ≫ f))
    ((isGrpPullback_pullback D'.P.A (thick R' I e)).comp h)
  obtain ⟨κ, hκ, -⟩ := grpPullback_iso (isGrpPullback_pullback G (thick R' I e ≫ f))
    ((isGrpPullback_pullback ((Over.pullback f).obj G) (thick R' I e)).comp (isGrpPullback_pullback G f))
  refine nonempty_gtCoord_of_isGt hG R' I D' e _ (GtBaseChange.extBC (thick R' I e ≫ f) (extOf D)) β xe hβ
    (fun χ => ?_) (isGt_of_iso κ (GtBaseChange.isGt_extBC _ _ G d))
  refine LBIso.chartPull (chartPullOut D.P.L (D.Oφ (𝟙 _) (xe χ)) Oε _ _ fun k => ?_) (chartPullId _)
    (iso_linComb ((isGen_iff w).1 hw) _ Oε).symm
  rw [Category.assoc, Oφ_push h (hc χ) k, ← Category.assoc]
  exact congrArg (· ≫ _) ((Category.assoc _ _ _).trans hβ')

end Datum

theorem exists_iso_of_generic (h : HomExtSt) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing K] (hK : IsField K) [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback (spMap (algebraMap T K))).obj G ≅ (Over.pullback (spMap (algebraMap T K))).obj G')
    (hf : IsMonHom f.hom) : ∃ F : G ≅ G', IsMonHom F.hom := by
  letI := hK.toField
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := h T K G G' hG hG' f.hom hf
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := h T K G' G hG' hG f.inv inferInstance
  refine ⟨⟨F, F', (h T K G G hG hG (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩,
    (h T K G' G' hG' hG' (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩⟩, hF⟩
  · rw [Functor.map_comp, eF, eF']
    exact f.hom_inv_id
  · rw [Functor.map_comp, eF, eF']
    exact f.inv_hom_id

theorem mk_C_constantCoeff {A : Type} [CommRing A] {J : Ideal (PowerSeries A)} (hJ : PowerSeries.X ∈ J)
    (s : PowerSeries A) : Ideal.Quotient.mk J (PowerSeries.C (PowerSeries.constantCoeff s)) = Ideal.Quotient.mk J s := by
  refine Ideal.Quotient.eq.2 (Ideal.mem_of_dvd J (PowerSeries.X_dvd_iff.2 ?_) hJ)
  simp

theorem bijective_mk_C (K : Type) [Field K] :
    Function.Bijective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K) ^ (0 + 1))).comp
      (PowerSeries.C (R := K))) := by
  have : Nontrivial (PowerSeries K ⧸ IsLocalRing.maximalIdeal (PowerSeries K) ^ (0 + 1)) := by
    rw [zero_add, pow_one]; infer_instance
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨_, mk_C_constantCoeff ?_ s⟩
  rw [zero_add, pow_one, PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span rfl

end GlobalTheory.ArcSplit

namespace GlobalTheory

open ArcSplit

theorem splitOver_of_hasArcData : Laws → Laws2 → Laws3 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b), IsDiscreteValuationRing O' → ∀ (χ : Sp (PowerSeries O') ⟶ Y.X) (t : SAB H (Sp (PowerSeries O'))) (_ : SABMap t Y.t χ), Y.HasArcData a (IsLocalRing.maximalIdeal (PowerSeries (FractionRing O'))) ((PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _)) PowerSeries.X (spMap (PowerSeries.map (algebraMap O' (FractionRing O'))) ≫ χ) → SplitOver t.G (Ideal.span {(PowerSeries.X : PowerSeries O')}) := by
  intro hL _ _ hExt E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a hO χ t m hA
  obtain ⟨t', m', P, φ, -, w, e, hφ, hw, -, -, hc, -⟩ := hA
  have hG := hL.globalFns
  obtain ⟨G, _, hGs, hGt⟩ := exists_isSemiAbelian_isGt hG _ (extOf a.D₀)
  have := hGs.comm
  let K' := FractionRing O'
  let I := IsLocalRing.maximalIdeal (PowerSeries K')
  let K := PowerSeries K' ⧸ I ^ (0 + 1)
  let f : O' →+* PowerSeries K' := (PowerSeries.C (R := K')).comp (algebraMap O' K')
  have hb := bijective_mk_C K'
  let ε : K' ≃+* K := RingEquiv.ofBijective _ hb
  have hK : IsField K := ε.symm.toMulEquiv.isField (Field.toIsField K')
  letI : Algebra O' K := ((Ideal.Quotient.mk (I ^ (0 + 1))).comp f).toAlgebra
  have : IsFractionRing O' K :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors O') (AlgEquiv.ofRingEquiv (f := ε) fun _ => rfl)
  have hX : PowerSeries.X ∈ I ^ (0 + 1) := by
    rw [zero_add, pow_one, show I = _ from PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  obtain ⟨g'⟩ := nonempty_coord_pullback hG hφ w hw e.symm.toAddEquiv
    (fun y => by have := hc (e.symm y); rwa [e.apply_symm_apply] at this) I 0 G hGt
  obtain ⟨F₁, hF₁⟩ := exists_iso_of_coord hG (P.U.gt 0) g'
  let ev : PowerSeries O' →+* O' := PowerSeries.constantCoeff
  let A := (Over.pullback (spMap ev)).obj t.G
  have e₁ : thick (PowerSeries K') I 0 ≫ spMap f = spMap (algebraMap O' K) := (spMap_comp _ _).symm
  have e₂ : thick (PowerSeries K') I 0 ≫ spMap (PowerSeries.map (algebraMap O' K')) =
      spMap (algebraMap O' K) ≫ spMap ev := by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap (RingHom.ext fun s => ?_)) (spMap_comp _ _))
    refine (mk_C_constantCoeff hX _).symm.trans (congrArg (fun x => Ideal.Quotient.mk _ (PowerSeries.C x)) ?_)
    rfl
  obtain ⟨F₀, hF₀, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback A (spMap (algebraMap O' K))).comp (isGrpPullback_pullback t.G (spMap ev))).comp m.cart)
    (((isGrpPullback_pullback t'.G (thick (PowerSeries K') I 0)).comp m'.cart).congr
      (by rw [← Category.assoc, e₂]) rfl)
  obtain ⟨F₂, hF₂, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (thick (PowerSeries K') I 0)).comp (isGrpPullback_pullback G (spMap f))).congr e₁ rfl)
    (isGrpPullback_pullback G (spMap (algebraMap O' K)))
  obtain ⟨F, hF⟩ := exists_iso_of_generic hExt O' K hK A G (IsSemiAbelian.pullback _ t.G t.semi) hGs
    (F₀ ≪≫ F₁ ≪≫ F₂) (inferInstanceAs (IsMonHom (F₀.hom ≫ F₁.hom ≫ F₂.hom)))
  have : IsMonHom F.symm.hom := inferInstanceAs (IsMonHom F.inv)
  obtain ⟨d⟩ := isGt_of_iso F.symm hGt
  let J : Ideal (PowerSeries O') := Ideal.span {PowerSeries.X}
  let s : O' →+* PowerSeries O' ⧸ J := (Ideal.Quotient.mk J).comp PowerSeries.C
  have e₃ : spMap s ≫ spMap ev = spMap (Ideal.Quotient.mk J) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext (mk_C_constantCoeff (Ideal.subset_span rfl))))
  obtain ⟨F₃, hF₃, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback A (spMap s)).comp (isGrpPullback_pullback t.G (spMap ev))).congr e₃ rfl)
    (isGrpPullback_pullback t.G (spMap (Ideal.Quotient.mk J)))
  exact ⟨_, isGt_of_iso F₃ (GtBaseChange.isGt_extBC (spMap s) _ A d)⟩

end GlobalTheory
