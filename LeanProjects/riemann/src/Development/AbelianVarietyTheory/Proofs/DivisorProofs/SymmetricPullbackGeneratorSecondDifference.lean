import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UTau0.SecondDiff

theorem prod_symmetricPullback_formalSum_eq {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) {T : Over (Sp R)}
    (q : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D₀.P.A.left) → U) :
    ∏ i, h (q.left ≫ GlobalTheory.UTau0.w0φ D₀ f i) ^ GlobalTheory.UTau0.w0ε i =
      h (q * (q ≫ f)).left * (h q.left ^ 2)⁻¹ * (h (q ≫ f).left)⁻¹ * h (1 : T ⟶ D₀.P.A).left ^ 2 := by
  have e₀ : q.left ≫ (padd D₀.P.A (𝟙 _) f).left = (q * (q ≫ f)).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ padd D₀.P.A (𝟙 _) f = q * (q ≫ f) from (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
  have e₃ : q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : T ⟶ D₀.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ toUnit D₀.P.A ≫ η[D₀.P.A] = 1 by rw [Hom.one_def, ← Category.assoc, comp_toUnit])
  rw [Fin.prod_univ_four]
  show h (q.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * h (q.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (q.left ≫ f.left) ^ (-1 : ℤ) * h (q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
  rw [e₀, e₃, Category.comp_id, ← Over.comp_left]
  simp only [zpow_one, zpow_neg, zpow_ofNat, pow_one]

theorem uw_second_diff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f g : D₀.P.A ⟶ D₀.P.A) [IsMonHom f] [IsMonHom g],
    padd D₀.P.A f g = 𝟙 D₀.P.A →
    ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A f g) rosatiε), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x x' : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw (x * x').left z J * cubV D₀.cub z J (x' ≫ f) (x' ≫ g) x =
        val uw x.left z J * val uw x'.left z J * val u (lift x x').left z J *
          cubV D₀.cub z J (x ≫ f) (x' ≫ f) x * cubV D₀.cub z J (x ≫ f) (x' ≫ f) x' *
          cubV D₀.cub z J x x' ((x ≫ f) * (x' ≫ f)) := by
  intro R _ _ D₀ f g _ _ hfg uw huw hw0 u hu hu0 T x x' z J hJ
  let p₀ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := fst _ _
  let p₁ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := snd _ _
  have mf : ∀ {T : Over (Sp R)} (a b : T ⟶ D₀.P.A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => MonObj.mul_comp a b f
  have fg : ∀ {T : Over (Sp R)} (a : T ⟶ D₀.P.A), (a ≫ f) * (a ≫ g) = a := fun a =>
    (MonObj.comp_mul _ _ _).symm.trans ((congrArg (a ≫ ·) (show f * g = 𝟙 _ from hfg)).trans (Category.comp_id a))
  let gLw := LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (p₀ * p₁).left)
    (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₁ ≫ f) (lift (p₁ ≫ g) p₀)).left)
  let gRw := LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw p₀.left)
      (LB.pullGen D₀.P.L _ _ uw p₁.left)) (LB.pullGen D₀.P.L _ _ u (lift p₀ p₁).left))
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₀)).left)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₁)).left))
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift p₀ (lift p₁ ((p₀ ≫ f) * (p₁ ≫ f)))).left))
  have vq : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      ∀ {K : Type} [Fintype K] {φ : K → (D₀.P.A.left ⟶ D₀.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D₀.P.L φ ε))
        (q : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A), val (LB.pullGen D₀.P.L _ _ t q.left) σ.left z J = val t (σ ≫ q).left z J :=
    fun σ z J hJ K _ φ ε t q => by rw [val_pull hJ, ← Over.comp_left]
  have evL : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gLw σ.left z J = val uw (σ ≫ (p₀ * p₁)).left z J *
        cubV D₀.cub z J (σ ≫ p₁ ≫ f) (σ ≫ p₁ ≫ g) (σ ≫ p₀) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (val_cub D₀.cub σ hJ _ _ _))
  have evR : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gRw σ.left z J = val uw (σ ≫ p₀).left z J * val uw (σ ≫ p₁).left z J *
          val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J *
        (cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₀) * cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₁) *
          cubV D₀.cub z J (σ ≫ p₀) (σ ≫ p₁) (σ ≫ ((p₀ ≫ f) * (p₁ ≫ f)))) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (vq σ hJ _ _)))
      (by rw [val_pull hJ, ← Over.comp_left, comp_lift])))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub D₀.cub σ hJ _ _ _) (val_cub D₀.cub σ hJ _ _ _))) (val_cub D₀.cub σ hJ _ _ _))))

  let e : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A ⊗ D₀.P.A := lift 1 1
  have he : e.left ≫ (snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
  have sj : Function.Surjective ((snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D₀.P.isAb _) ((GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2)
  let ρ : T ⟶ D₀.P.A ⊗ D₀.P.A := lift x x'
  have key : val gLw ρ.left z J = val gRw ρ.left z J := by
    refine gen_unique' D₀.P.isLB (fun V _ k => ?_) _ e.left he sj ?_ ?_ (fun y I hI => ?_) _ ρ.left z J hJ
    · refine Eq.trans (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ Fin 6) (K' := (thK ⊕ thK) ⊕ thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 6) (U := V) _
            (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f p₀ k) (prod_symmetricPullback_formalSum_eq D₀ f p₁ k))
            (prod_ros f g p₀ p₁ k))
          (DVR.prod_sum₂ (K := thK ⊕ thK) (K' := thK) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₀ k)
              (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₁ k))
            (prod_cub p₀ p₁ ((p₀ ≫ f) * (p₁ ≫ f)) k)))
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f (p₀ * p₁) k)
          (prod_cub (p₁ ≫ f) (p₁ ≫ g) p₀ k)).symm)
      rw [mf, fg, mul_comm p₁ p₀, mul_comm (p₀ ≫ f) p₀, mul_comm (p₁ ≫ f) p₁, mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₀,
        mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₁, mul_comm (p₁ ≫ g) p₀]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ huw _)) (DVR.pullGen_isGen _ _ _ _ hu _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
          (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _))
    · have C : IsCub (cubV D₀.cub y I) := isCub_cubV D₀.cub hI
      have w1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI hw0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by simp [Hom.one_def]
        rw [e1]; exact this
      have u1 : val u (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1).left y I = 1 := by
        have := val_corr hI hu0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e2 : lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1 = lift η[D₀.P.A] η[D₀.P.A] := by simp [Hom.one_def]
        rw [e2]; exact this
      have a₀ : e ≫ p₀ = 1 := lift_fst _ _
      have a₁ : e ≫ p₁ = 1 := lift_snd _ _
      have af : e ≫ p₀ ≫ f = 1 := by rw [← Category.assoc, a₀, MonObj.one_comp]
      have bf : e ≫ p₁ ≫ f = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have bg : e ≫ p₁ ≫ g = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have ab : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
      have ff : e ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [af, bf, _root_.mul_one])
      rw [evL e hI, evR e hI, ab, ff, af, bf, bg, a₀, a₁, w1, u1, C.face]
      simp
  rw [evL ρ hJ, evR ρ hJ] at key
  have r₀ : ρ ≫ p₀ = x := lift_fst _ _
  have r₁ : ρ ≫ p₁ = x' := lift_snd _ _
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  have s₂ : ρ ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = (x ≫ f) * (x' ≫ f) :=
    (MonObj.comp_mul _ _ _).trans (by rw [← Category.assoc, ← Category.assoc, r₀, r₁])
  rw [s₁, s₂, ← Category.assoc ρ p₁ f, ← Category.assoc ρ p₁ g, ← Category.assoc ρ p₀ f, r₀, r₁] at key
  rw [key]
  simp only [_root_.mul_assoc]

end GlobalTheory.UTau0.SecondDiff
