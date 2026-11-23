import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaSquare
open GlobalTheory.SymLiftOdd GlobalTheory.UT.SymFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem eq_liftFun_mul (hL : L.IsLB) {k : ℤ} (s s' : LB.Sec (LPow A L k T)) (a : Γ(T.left, ⊤))
    (h : ∀ y J, Good L y J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y J =
        gs (fst T A).left y ⊤ a * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y J)
    (j) : s'.f j = liftFun A _ a * s.f j := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have e₁ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₂ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (liftFun A ((LPow A L k T).U j) a) = gs (fst T A).left y ⊤ a :=
    (gs_res (𝟙 _) y le_top hy _).trans ((gs_pull (𝟙 _) (fst T A).left y ⊤ trivial a).trans (by rw [Category.id_comp]))
  refine e₁.trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  exact (congrArg _ (h y I hI)).trans (mul_left_comm _ _ _)

theorem indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {P v} (h : GRep L (T ⊗ A) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), P U h = 1) (m m' : T ⊗ A ⟶ A)
    (y : (T ⊗ A).left) (J) (hJ : Good L y J) : v _ (lift (fst T A) m) y J = v _ (lift (fst T A) m') y J := by
  obtain ⟨K, _, φ, ε, s, hs, p, hv⟩ := h
  obtain ⟨a, ha⟩ := exists_constT hG hA hL (fun U _ h => (p U h).trans (hP U h)) hs
  exact (hv _ _ y J hJ).symm.trans ((ha m y J hJ).trans ((ha m' y J hJ).symm.trans (hv _ _ y J hJ)))

theorem grep_sigma {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    {Y : Over S} (w : Y ⟶ A) :
    GRep L Y (fun _ _ h => h (w⁻¹).left * (h w.left)⁻¹) (fun _ r z J => val σ (r ≫ w).left z J) :=
  (grep_gen σ hσ w.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (w⁻¹).left ^ (1 : ℤ) * h (w.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_two {n : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, n.left] ![a, b])} (hα : α.IsGen) (w : T ⊗ A ⟶ A) :
    GRep L (T ⊗ A) (fun _ _ h => h w.left ^ a * h (lift (fst T A) w ≫ n).left ^ b)
      (fun _ r z J => val α (r ≫ lift (fst T A) w).left z J) :=
  (grep_gen α hα (lift (fst T A) w).left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (lift (fst T A) w ≫ snd T A).left ^ a * h (lift (fst T A) w ≫ n).left ^ b = _
      rw [lift_snd])
    (fun _ _ _ _ _ => rfl)

theorem square_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    (hσ₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ σ (eSec A)) (LB.oneGen L))
    (θ : ThetaGrp A L ((4 : ℕ) : ℤ) T) (hx : θ.pt ^ 4 = 1) (nu : LB.Gen (negLB A L ((4 : ℕ) : ℤ) T))
    (hnu : ∀ y J, Good L y J → ∀ m, negVal nu y J m = (val σ m.left y J ^ 4)⁻¹)
    (hs : LB.Gen.Corr L _ _ _ _ (symGen A L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen L))
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ 2).left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])}
    (hα : α.IsGen) (y : (T ⊗ A).left) (J) (hJ : Good L y J) :
    thetaVal θ y J (snd T A) * (thetaVal θ y J ((fst T A ≫ θ.pt) * snd T A) *
      val α (lift (fst T A) ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))).left y J) =
      val σ ((fst T A ≫ θ.pt) ^ 2).left y J * val α (lift (fst T A) (snd T A)).left y J := by
  have := hA.comm
  have hX : (fst T A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have s₁ : val σ (1 : T ⊗ A ⟶ A).left y J = 1 :=
    (val_pull hJ σ (eSec A) (T ⊗ A).hom).symm.trans ((val_corr hJ hσ₁ _).trans (val_one _))
  have sy := (val_symGen θ nu rfl hJ 1).symm.trans ((val_corr hJ hs _).trans (val_one _))
  rw [hnu y J hJ, hnu y J hJ, s₁, _root_.mul_one, inv_one] at sy
  have gθ := fun w => grep_two (L := L) (n := translPt A θ.pt) (a := ((4 : ℕ) : ℤ)) (b := -((4 : ℕ) : ℤ))
    (α := θ.φ) θ.isGen w
  have cl : ∀ m w : T ⊗ A ⟶ A, lift (fst T A) m ≫ lift (fst T A) w = lift (fst T A) (lift (fst T A) m ≫ w) :=
    fun m w => by rw [comp_lift, lift_fst]
  have H₁ := indep hG hA hL (((gθ (snd T A)).mul ((gθ ((fst T A ≫ θ.pt) * snd T A)).mul
    (grep_two hα ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))))).mul (grep_two hα (snd T A)).inv)
    (fun U _ h => by
      have e : ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A)) ^ 2 = snd T A ^ 2 := by
        rw [← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
      simp only [lift_translPt, MonObj.comp_pow, lift_snd, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (snd T A) (fst T A ≫ θ.pt)⁻¹ y J hJ
  have H₂ := indep hG hA hL ((((grep_sigma hσ (snd T A)⁻¹).pow 4).inv.mul ((grep_two hα (snd T A)).mul
    (grep_two hα (snd T A)⁻¹).inv)).mul (grep_sigma hσ (snd T A ^ 2)).inv)
    (fun U _ h => by
      simp only [MonObj.comp_pow, lift_snd, inv_inv, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) (fst T A ≫ θ.pt) 1 y J hJ
  simp only [cl, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, lift_snd, lift_fst_assoc, mul_inv_cancel, _root_.mul_one,
    inv_one, one_pow, s₁] at H₁ H₂
  replace H₁ := congrArg Additive.ofMul H₁
  replace H₂ := congrArg Additive.ofMul H₂
  replace sy := congrArg Additive.ofMul sy
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, thetaVal] at H₁ H₂ sy ⊢
  linear_combination (norm := module) H₁ + H₂ + sy

theorem exists_symmetric_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  intro R _ _ A F _ _ _ x hx σ hσ hσ₁
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hL := A.isLB
  have := A.isAb.comm
  obtain ⟨θ₀, h₀⟩ := GlobalTheory.ThetaLift.exists_theta_of_field (FractionRing R) A (TFK (R := R) F) F (Iso.refl _) 4 x hx
  obtain ⟨nu, hnu, vn⟩ := ((grep_sigma hσ (snd (TFK (R := R) F) A.A)).pow 4).inv.out hL
    ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ ι[A.A]).left] ![((4 : ℕ) : ℤ), -((4 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (snd (TFK (R := R) F) A.A).left ^ ((4 : ℕ) : ℤ) * h ((snd (TFK (R := R) F) A.A)⁻¹).left ^ (-((4 : ℕ) : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  have vn' : ∀ y J, Good A.L y J → ∀ m, negVal (L := A.L) (k := ((4 : ℕ) : ℤ)) nu y J m = (val σ m.left y J ^ 4)⁻¹ :=
    fun y J hJ m => (vn _ _ y J hJ).trans (by beta_reduce; rw [lift_snd])
  obtain ⟨a, ha⟩ := exists_symConst hG A.isAb hL θ₀ (nu := nu) hnu
  obtain ⟨b, hb⟩ : ∃ b : Γ((TFK (R := R) F).left, ⊤)ˣ, a = b ^ 2 := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (e a.val) two_pos
    have e₁ : (e.symm r) ^ 2 = a.val := by rw [← map_pow, hr, RingEquiv.symm_apply_apply]
    have u : IsUnit (e.symm r) := (isUnit_pow_iff two_ne_zero).1 (e₁ ▸ a.isUnit)
    exact ⟨u.unit, Units.ext e₁.symm⟩
  obtain ⟨θ, hpt, hv⟩ := exists_scale hL θ₀ b⁻¹
  have hθ : θ.pt = x := hpt.trans h₀
  have hs : LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L) := corr_of_val hL fun y J hJ => by
    have e₁ := (val_symGen θ₀ nu h₀ hJ (snd _ _)).symm.trans (ha _ y J hJ)
    rw [val_one, id_eq_lift, val_symGen θ nu hθ hJ, hv y J hJ, hv y J hJ, map_inv]
    rw [hb, map_pow] at e₁
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ ⊢
    linear_combination (norm := module) e₁
  obtain ⟨K, _, φ, ε, s, hs', p, vs⟩ := grep_sigma hσ (x ^ 2)
  obtain ⟨c, hc⟩ := H1.exists_const A.L hL (𝟙 _) (fun v => ⟨v, by simp⟩) s hs' (fun U _ h => (p U h).trans (by
    have e : (x ^ 2)⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hx
    beta_reduce
    rw [e, mul_inv_cancel]))
  have ec : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, hθ, ⟨nu, hnu, hs⟩, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun z J hJ => ?_, ?_⟩
  · have e₁ := vs _ (𝟙 _) z J hJ
    have e₂ := hc _ (𝟙 _) z J hJ
    beta_reduce at e₁
    rw [Category.id_comp, Over.id_left] at e₁
    rw [Category.id_comp] at e₂
    exact (congrArg Units.val e₁).symm.trans (e₂.trans (congrArg (gs _ z ⊤) ec.symm))
  · rintro ψ m hm hψ rfl α hα t t₁ t₂ t₃ h₁ h₂ h₃ j
    rw [ec]
    refine eq_liftFun_mul hL t₁ t₃ c (fun y J hJ => ?_) j
    subst hθ
    have key := square_val hG A.isAb hL hσ hσ₁ θ hx nu vn' hs hα y J hJ
    have e₁ := vs _ (fst _ A.A) y J hJ
    have e₂ := hc _ (fst _ A.A).left y J hJ
    beta_reduce at e₁
    rw [MonObj.comp_pow] at e₁
    rw [Category.comp_id, e₁] at e₂
    have hX : (fst (TFK (R := R) F) A.A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have eψ : lift (fst (TFK (R := R) F) A.A) ((fst _ _ ≫ θ.pt) * ((fst _ _ ≫ θ.pt) * snd _ _)) ≫ ψ =
        lift (fst _ _) (snd _ _) ≫ ψ := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hψ, lift_fst, lift_fst]
      · rw [Category.assoc, Category.assoc, hm, MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd,
          ← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
    rw [← e₂, id_eq_lift, ThetaLin.sval_of_isTwistPull A.A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₂ _ y hJ,
      ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ]
    simp only [← Over.comp_left]
    rw [lift_translT, lift_translT, eψ]
    have alg : ∀ {M : Type} [CommMonoid M] (a b c d e : Mˣ) (w : M), a * (b * c) = d * e →
        a.val * (b.val * (c.val * w)) = d.val * (e.val * w) := fun a b c d e w h => by
      have h' := congrArg (fun u => Units.val u * w) h
      simpa only [Units.val_mul, _root_.mul_assoc] using h'
    exact alg _ _ _ _ _ _ key

end GlobalTheory.ThetaSquare

end
