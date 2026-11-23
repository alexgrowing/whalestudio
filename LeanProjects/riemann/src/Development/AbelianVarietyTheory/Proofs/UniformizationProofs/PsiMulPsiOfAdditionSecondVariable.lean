import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionFirstVariable
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_zero (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := cT_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem cT_neg (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a : D.X) : cT D T (-a) = (cT D T a)⁻¹ := by
  have h := cT_add D T a (-a)
  rw [add_neg_cancel, cT_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem val_sym_one (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have a := val_corr hJ D.sym_rig T.hom
  rw [val_one] at a
  refine Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans a)
  congr 1

theorem one_kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : T ⟶ D.P.A) :
    kapV D a b z J 1 y = (val D.sym y.left z J)⁻¹ * rigV D z J ^ 2 * cubV D.cub z J (cT D T b) y y⁻¹ *
      (cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹ := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0]
  simp only [h.face₃, h.face₂, h.face, _root_.mul_one, _root_.one_mul]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J ≠ 0)
    (h0' : sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * (sval (s' i 0) (lift ρ (y * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val *
        ((val (D.psi mu) κ.left z J).val * (val (D.psi (-mu)) κ.left z J).val *
          (val D.sym (y * cT D T mu).left z J).val) =
      C * (U * (val (D.psi 0) κ.left z J).val * (val (D.psi 0) κ.left z J).val) *
        ((cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y).val * (val D.sym y.left z J).val) := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  have e₁ := (hA T ρ 1 y z J hJ).1 mu (-mu) 0 (0 + 2 • mu) (by abel) (by rw [two_smul]; abel)
  have e₂ := (hA T ρ 1 (y * cT D T mu) z J hJ).1 0 0 0 0 (by abel) (by abel)
  rw [one_kapV D _ _ hJ, _root_.one_mul y, _root_.one_mul y⁻¹, hP _ T ρ κ _ z J hJ,
    hP (-mu) T ρ κ _ z J hJ] at e₁
  rw [one_kapV D _ _ hJ, _root_.one_mul (y * cT D T mu), _root_.one_mul (y * cT D T mu)⁻¹, mul_inv y, ← cT_neg,
    hP 0 T ρ κ (y * cT D T mu) z J hJ, hP 0 T ρ κ (y⁻¹ * cT D T (-mu)) z J hJ, cT_zero, h.face, h.face₂,
    _root_.mul_one (y * cT D T mu), _root_.mul_one (y⁻¹ * cT D T (-mu))] at e₂
  have e₃ : ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * U * ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i 0) (lift ρ (y * cT D T mu)).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  generalize val D.sym y.left z J = A at e₃ ⊢
  generalize val D.sym (y * cT D T mu).left z J = B at e₃ ⊢
  generalize cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y = E at e₃ ⊢
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * (A⁻¹ * B⁻¹ * E⁻¹ * rigV D z J ^ 4).val *
      sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J *
      sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) h0) h0'
  refine mul_left_cancel₀ hne ?_
  have a := A.mul_inv
  have b := B.mul_inv
  have e := E.mul_inv
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, inv_one, Units.val_one] at e₃ ⊢
  generalize gs (𝟙 _) z ⊤ (scal T.hom r) = g at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J = p at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J = q at e₃ ⊢
  generalize (rigV D z J).val = w at e₃ ⊢
  generalize (val (D.psi mu) κ.left z J).val = m at e₃ ⊢
  generalize (val (D.psi (-mu)) κ.left z J).val = m' at e₃ ⊢
  generalize (val (D.psi 0) κ.left z J).val = o at e₃ ⊢
  generalize (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val = k at e₃ ⊢
  linear_combination e₃ + g * A⁻¹.val * E⁻¹.val * w ^ 4 * p * q * k * m * m' * b -
    g * B⁻¹.val * w ^ 4 * p * q * C * U * o * o * (E.val * E⁻¹.val * a + e)

theorem isIso_refl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ)) := by
  have e : lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) ≫
      lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) = 𝟙 _ := by
    ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv, inv_inv,
        inv_mul_cancel_right, Category.id_comp]
  exact ⟨_, e, e⟩

end SecondPosition

open FirstSlot SecondPosition in

theorem psi_mul_psi_of_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 mu α hα c u hs z J hJ
  subst hα
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hint : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let κF : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have zf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have zs : DegPre.zF D F ≫ snd _ _ = 1 := lift_snd _ _
  have zκ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A ≫ κF).left = jFK (R := R) F := by
    rw [← Over.comp_left, ← Category.assoc, zf, Category.id_comp]; rfl
  have hJ' : Good D.P.L ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) := fun ψ => hJ _
  have hhom : (DegPre.BF D F).hom = (fst (TF (R := R) F) D.P.A ≫ κF).left ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A ≫ κF)).symm
  have key := SecondPosition.compare D (TF (R := R) F) s₀ r s s' hA hP mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (by
      have := isIso_transl D (TF (R := R) F) mu
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) mu)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) mu))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    (by
      have := isIso_refl D (TF (R := R) F) (-mu)
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (DegPre.BF D F) (-mu))).left :=
        (Over.forget _).map_isIso
          (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (TF (R := R) F ⊗ D.P.A) (-mu)))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    _ _ (fun i => by
      rw [lift_fst_snd]
      exact hs i _ _ hJ')
  have ψn : ∀ χ, ((DegPre.zF D F).left.stalkMap z).hom (val (D.psi χ) (fst (TF (R := R) F) D.P.A ≫ κF).left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J).val := fun χ => by
    rw [← zκ]
    exact ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 (D.psi χ)).symm
  have cn : ∀ x x' y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (cubV D.cub
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) x x' y).val =
      (cubV D.cub z J (DegPre.zF D F ≫ x) (DegPre.zF D F ≫ x') (DegPre.zF D F ≫ y)).val := fun x x' y => by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.cub.t).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have sn : ∀ y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (val D.sym y.left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val D.sym (DegPre.zF D F ≫ y).left z J).val := fun y =>
    ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.sym).symm
  have un : ((DegPre.zF D F).left.stalkMap z).hom (val u (𝟙 _)
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val u (DegPre.zF D F).left z J).val := by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 u).symm.trans ?_
    rw [Category.comp_id]
  have kn : ((DegPre.zF D F).left.stalkMap z).hom (gs (𝟙 _) ((DegPre.zF D F).left z) ⊤ (DegPre.constBF D F c ⊤)) =
      gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) := by
    refine (gs_comp_stalkMap (𝟙 _) (DegPre.zF D F).left z ⊤ trivial _).symm.trans ?_
    refine (gs_res ((DegPre.zF D F).left ≫ 𝟙 _) z (U := ⊤) (V := ⊤) le_top trivial _).trans ?_
    refine (gs_pull ((DegPre.zF D F).left ≫ 𝟙 _) (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
    rw [Category.comp_id, ← Over.comp_left, zf]
    rfl
  have h := isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, cn, cn, sn, sn, un, kn, MonObj.comp_mul, zs, h.face₂, h.face₃, comp_cT, _root_.one_mul (cT D _ mu),
    val_sym_one D hJ, Units.val_one, _root_.one_mul, _root_.one_mul, _root_.mul_one] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
