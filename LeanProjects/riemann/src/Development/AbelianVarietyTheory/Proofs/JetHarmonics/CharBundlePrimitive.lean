import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open CoordToExt

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev charBundle (χ : D.X) : LB D.P.A.left := LB.LinComb D.P.L (D.Oφ (𝟙 D.P.A) χ) Oε

theorem comp_Oφ_id {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem charBundle_rig (χ : D.X) : ∃ t : LB.Gen ((charBundle D χ).pull (eSec D.P.A)), t.IsGen := by
  refine ((refines_self _ _).linComb (fun _ : PUnit => eSec D.P.A) (fun _ => 1)).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ?_)
  have e : (η[D.P.A] : 𝟙_ _ ⟶ D.P.A) = 1 := by simp [Hom.one_def]
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  simp only [_root_.mul_one, eSec, comp_Oφ_id]
  refine (prod_O D η[D.P.A] χ h).trans ?_
  rw [e, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_add (χ χ' : D.X) :
    ∃ t : LB.Iso (charBundle D χ') (LB.div (charBundle D (χ + χ')) (charBundle D χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (𝟙 D.P.A))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (𝟙 D.P.A) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (𝟙 D.P.A) _ h) (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h)))
    (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem charBundle_zero : ∃ t : LB.Gen (charBundle D 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (𝟙 D.P.A) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ D.P.A (charBundle D χ)), t.IsGen := by
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

def splitExt : SplitExt (Spec (CommRingCat.of R)) where
  B := D.P.A
  isAbelian := D.P.isAb
  X := D.X
  O χ := ⟨charBundle D χ, (charBundle_rig D χ).choose, DVR.linComb_isLB _ D.P.isLB _ _,
    (charBundle_rig D χ).choose_spec⟩
  addIso := charBundle_add D
  zeroTriv := charBundle_zero D
  primitive := charBundle_primitive D

variable {D} {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]

theorem nonempty_gtCoord (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) (I : Ideal R) (e : ℕ) :
    Nonempty (GtCoord I D e H) := by
  obtain ⟨d⟩ := h
  refine nonempty_gtCoord_of_isGt hG R I D e H (GtBaseChange.extBC (thick R I e) (splitExt D)) (Iso.refl _)
    (AddEquiv.refl _) (inferInstanceAs (IsMonHom (𝟙 (thickObj R I e D.P.A)))) (fun χ => ?_)
    (GtBaseChange.isGt_extBC _ _ H d)
  refine ((refines_self _ _).div ((refines_self (D.Oφ (𝟙 D.P.A) χ) Oε).linComb
    (fun _ : PUnit => pullback.fst D.P.A.hom (thick R I e)) (fun _ => 1))).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_prod_type, mul_inv_eq_one, eq_comm, Fintype.prod_unique]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.mul_one]
  have e₀ : ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e).left =
      pullback.fst D.P.A.hom (thick R I e) := Category.id_comp _
  exact congrArg (fun q => h (q ≫ D.Oφ (𝟙 D.P.A) χ k) ^ Oε k) e₀.symm

instance isIso_thick_bot : IsIso (thick R ⊥ 0) := by
  have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk ((⊥ : Ideal R) ^ (0 + 1)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (Ideal.Quotient.mk_bijective_iff_eq_bot _ |>.2 (by simp))
  infer_instance

instance isIso_fstG_bot : IsIso (fstG (⊥ : Ideal R) 0 H).left :=
  inferInstanceAs (IsIso (pullback.fst H.hom (thick R ⊥ 0)))

theorem exists_points (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T,
      (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
        GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x')) := by
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

end GlobalTheory.TorusModel
