import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace FamPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

theorem sval_eq_of_app_injective {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Sec (LB.LinComb M φ ε)} {u' : LB.Sec (LB.LinComb M φ' ε')}
    (h : ∀ y J, Good M y J → sval u κ y J = sval u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : sval u r z J = sval u' r z J := by
  obtain ⟨t, hv⟩ := exists_sec hM hF u'
  have e : ∀ j, u.f j = t.f j := fun j => by
    refine hκ (LB.wchart M φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ ((h y I hI).trans (hv _ κ y I hI).symm)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)
  exact (congrArg (gs r z _) (e _)).trans (hv Z r z J hJ)

section One

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem comp_famφB {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (α : D.X) (i : Fin 4) :
    x.left ≫ D.famφB α i = (![x, cP D T α * x, cP D T α, 1] i).left := by
  fin_cases i
  · exact Category.comp_id _
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul x (𝟙 _) (cP D _ α)).trans
      (by rw [comp_cP, Category.comp_id, mul_comm]))
  · exact congrArg (fun q => q.left) (comp_cP D x α)
  · exact congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) x)

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (x.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h x.left ^ ((k : ℤ) - 1) * h (cP D T α * x).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, comp_famφB, comp_famφB, comp_famφB, comp_famφB]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def feUnit (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (ψ : D.X → (T.left.presheaf.stalk z)ˣ) (ρ : (T.left.presheaf.stalk z)ˣ) :
    (T.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T α) (cP D T mu) x * (th D z J (cP D T α) x (cP D T mu))⁻¹ *
    (ψ (mu + α) * (ψ mu)⁻¹ * (ψ α)⁻¹ * ρ⁻¹ * (ψ mu ^ k * ρ ^ k))

variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_feUnit (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J =
      feUnit D k mu α (ρ ≫ DegPre.prB D F) z J (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
        (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) := by
  rw [val_famMult _ hJ, TauPull.val_tau _ hJ, uVal, comp_cP, comp_cP, feUnit]
  exact congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))

theorem comp_trF (mu : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) :
    (ρ.left ≫ (DegPre.trF D F mu).left) ≫ (DegPre.prB D F).left = ((ρ ≫ DegPre.prB D F) * cP D T mu).left := by
  rw [← Over.comp_left, ← Over.comp_left, Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, comp_cP, comp_cP]

theorem famFE_iff (hG : GlobalFnsSt) {k : ℕ} (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (f : ∀ α, D.SecB k α) (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D F).left 1) :
    DegPre.FamFE D F k s ↔ ∀ (mu α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → sval (f (α + k • mu)) (ρ ≫ DegPre.prB D F).left z J =
        sval (f α) ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J *
          (feUnit D k mu α (ρ ≫ DegPre.prB D F) z J
            (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
            (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)).val := by
  constructor
  · intro H mu α T ρ z J hJ
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H mu α u hu hc) _ ρ.left z J hJ
    rw [hv u hu hc T ρ z J hJ, val_feUnit k mu α ρ hJ, ← secScal_sval (hs _) _ z hJ, ← secScal_sval (hs _) _ z hJ,
      comp_trF] at e
    exact e
  · intro H mu α u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have e := H mu α _ (𝟙 _) y J hJ
    rw [← val_feUnit k mu α _ hJ, ← (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ, ← comp_trF,
      secScal_sval (hs _) _ y hJ, Over.comp_left, secScal_sval (hs _) _ y hJ] at e
    exact e

end One

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem exists_feGen (ψW : PsiOn D W) (k : ℕ) (mu α : D.X) :
    ∃ (K : Type) (_ : Fintype K) (φ : K → ((TW W ⊗ D.P.A).left ⟶ D.P.A.left)) (ε : K → ℤ)
      (u : LB.Gen (LB.LinComb D.P.L φ ε)), u.IsGen ∧
      FormEq (Sum.elim (fun i => (snd (TW W) D.P.A * cP D _ mu).left ≫ D.famφB α i) φ) (Sum.elim (DegPre.famε k) ε)
        (fun i => (snd (TW W) D.P.A).left ≫ D.famφB (α + k • mu) i) (DegPre.famε k) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TW W ⊗ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = feUnit D k mu α (ρ ≫ snd _ _) z J (fun χ => val (ψW.psi χ) (ρ ≫ fst _ _).left z J)
          (val (D.rigW W) (ρ ≫ fst _ _).left z J) := by
  let a : TW W ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : TW W ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : TW W ⊗ D.P.A ⟶ D.P.A := snd _ _
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m x k
  have hρ : (D.rigW W).IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  refine ⟨_, inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x m)).left)))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ψW.tau mu α) (LB.mulGen D.P.L _ _ _ _
        (GeneratorPullback.powGen D.P.L _ _ (ψW.psi mu) k) (GeneratorPullback.powGen D.P.L _ _ (D.rigW W) k))) (fst (TW W) D.P.A).left),
    mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
        (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _)
          (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ hρ))
        (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (ψW.psi_gen mu) k) (powGen_isGen _ _ _ _ hρ k))) _),
    fun U _ h => ?_, fun T ρ z J hJ => ?_⟩
  · have p₁ := prod_cub a x m h
    have p₃ := prod_famB D x (α + k • mu) k h
    have p₄ := prod_famB D (x * m) α k h
    have a₁ : ∀ χ, (fst (TW W) D.P.A).left ≫ (toUnit (TW W) ≫ D.c χ).left = (cP D (TW W ⊗ D.P.A) χ).left := fun χ =>
      congrArg (fun q => q.left) (comp_cP D (fst (TW W) D.P.A) χ)
    have a₂ : (fst (TW W) D.P.A).left ≫ (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⊗ D.P.A ⟶ D.P.A).left :=
      congrArg (fun q : TW W ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst (TW W) D.P.A))
    refine Eq.trans (prod_sum₂ (K := Fin 4) (U := U) _ p₄ (prod_sum₂ (K := Fin 8 ⊕ thK) (U := U) _
      (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) rfl)) (Eq.trans ?_ p₃.symm)
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α, cPoint_add, cPoint_add, cPoint_nsmul, ← _root_.mul_assoc (cP D _ α), mul_comm x m]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, m, x]
    module
  · refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
      ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (TauPull.val_tauW ψW _ hJ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))))))
    rw [comp_cP, comp_cP]

theorem fe_on (hG : GlobalFnsSt) (ψW : PsiOn D W) {k : ℕ} (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) (mu α : D.X)
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) (x : T ⟶ D.P.A) {z : T.left} {J} (hJ : Good D.P.L z J) :
    sval (f (α + k • mu)) x.left z J = sval (f α) (x * cP D T mu).left z J *
      (feUnit D k mu α x z J (fun χ => val (ψW.psi χ) κ.left z J) (val (D.rigW W) κ.left z J)).val := by
  obtain ⟨K, _, φ, ε, u, hu, hF, hv⟩ := exists_feGen ψW k mu α
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TW W ⊗ D.P.A) (z : T.left) (J), Good D.P.L z J →
      sval (pullSec D.P.L _ _ (f (α + k • mu)) (snd (TW W) D.P.A).left) ρ.left z J =
        sval (f (α + k • mu)) (ρ ≫ snd _ _).left z J ∧
      sval (pullMulSec (f α) (snd (TW W) D.P.A * cP D _ mu).left u hu) ρ.left z J =
        sval (f α) ((ρ ≫ snd _ _) * cP D T mu).left z J *
          (feUnit D k mu α (ρ ≫ snd _ _) z J (fun χ => val (ψW.psi χ) (ρ ≫ fst _ _).left z J)
            (val (D.rigW W) (ρ ≫ fst _ _).left z J)).val := fun T ρ z J hJ =>
    ⟨sval_pullSec _ _ _ _ _ z hJ, by
      rw [sval_pullMulSec _ _ _ _ _ z hJ, hv T ρ z J hJ, ← Over.comp_left, MonObj.comp_mul, comp_cP]⟩
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  let π : (TW W ⊗ D.P.A).left ⟶ W.toScheme := (fst (TW W) D.P.A).left
  have : Flat π := by
    have := D.P.isAb.smooth
    show Flat (pullback.fst _ _)
    infer_instance
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (jK R ∣_ W) π ≫ (TW W ⊗ D.P.A).hom)
  let h : T₀ ⟶ TW W ⊗ D.P.A := Over.homMk (pullback.snd (jK R ∣_ W) π) rfl
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have hc : (pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι) ≫ jK R = T₀.hom := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (pullback.snd (jK R ∣_ W) π ≫ ·) (Over.w (fst (TW W) D.P.A))
  let σ : T₀ ⟶ TF (R := R) (FractionRing R) := Over.homMk (pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι) (by
    show _ ≫ jFK (R := R) (FractionRing R) ≫ jK R = _
    rw [hj, Category.id_comp]; exact hc)
  have hinj : ∀ U : (TW W ⊗ D.P.A).left.Opens, Function.Injective (h.left.app U).hom := fun U =>
    (pullback.snd (jK R ∣_ W) π).app_injective U
  have H : ∀ (y : T₀.left) I, Good D.P.L y I →
      sval (pullSec D.P.L _ _ (f (α + k • mu)) (snd (TW W) D.P.A).left) h.left y I =
        sval (pullMulSec (f α) (snd (TW W) D.P.A * cP D _ mu).left u hu) h.left y I := fun y I hI => by
      obtain ⟨k₁, k₂⟩ := key T₀ h y I hI
      have e := (famFE_iff hG F.s f hs).1 F.fe mu α T₀ (lift σ (h ≫ snd _ _)) y I hI
      have hσ : σ.left ≫ jFK (R := R) (FractionRing R) = pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι :=
        (congrArg (σ.left ≫ ·) hj).trans (Category.comp_id _)
      rw [lift_snd, lift_fst] at e
      have b : (h ≫ fst _ _).left = pullback.fst (jK R ∣_ W) π ≫ jK R ∣_ W := pullback.condition.symm
      have vψ : ∀ χ, val (ψW.psi χ) (h ≫ fst _ _).left y I =
          val (D.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) y I := fun χ => by
        rw [b, hσ]
        exact (val_pull hI _ _ _).symm.trans ((val_corr hI (ψW.psi_eq χ) _).trans (val_pull hI _ _ _))
      have vρ : val (D.rigW W) (h ≫ fst _ _).left y I =
          val D.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) y I :=
        (val_pull hI _ _ _).trans (Eq.trans (congrArg (fun q => val D.rig q y I)
          ((Over.w (h ≫ fst _ _)).trans (hc.symm.trans (congrArg (· ≫ jK R) hσ.symm)))) (val_pull hI _ _ _).symm)
      rw [k₁, k₂, e, vρ, funext vψ]
  have E := sval_eq_of_app_injective D.P.isLB hF h.left hinj H T.left (lift κ x).left z J hJ
  obtain ⟨k₁, k₂⟩ := key T (lift κ x) z J hJ
  rw [lift_snd] at k₁
  rw [lift_fst, lift_snd] at k₂
  exact k₁.symm.trans (E.trans k₂)

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem val_psiW (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) {y : Z} {J J'}
    (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) (r ≫ hD.g) y J =
      (gw hD.w (r ≫ D'.xK χ) y (J ((r ≫ D'.xK χ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' (r ≫ D'.xK χ)))⁻¹ * val (D'.psi χ) r y J' := by
  obtain ⟨b, hb, hc⟩ := hD.psi_pr χ
  have e₂ := (val_corr hJ hc r).trans (val_pull hJ _ _ _)
  rw [← e₂]
  obtain ⟨p, hp⟩ : ∃ p, p = J ((r ≫ D'.xK χ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = J' (r ≫ D'.xK χ) := ⟨_, rfl⟩
  rw [← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [hp, Category.assoc]),
    val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => hq.symm)]
  have m₁ : r y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U
      (fun _ => p) ⊓ D'.P.L.U q) := ⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩
  have e₁ := congrArg (gm r y
    (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)))
    (hb (fun _ => p) q)
  refine (gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y
      ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_))
      (gm_res _ y _ m₁ _))))
  exact zpow_neg_one _

theorem cubN_twist {A U : Type} [CommGroup A] [CommGroup U] (θ θ' : A → A → A → U) (Ω : A → U)
    (h : ∀ a b c, θ a b c = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
      θ' a b c) (k : ℕ) (a m x : A) :
    cubN θ k a m x = Ω (a * m ^ k * x) * (Ω (a * m ^ k))⁻¹ * (Ω (a * x))⁻¹ * Ω a *
      ((Ω (m * x))⁻¹ * Ω m * Ω x * (Ω 1)⁻¹) ^ k * cubN θ' k a m x := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    rw [ih, h, pow_succ m, ← _root_.mul_assoc a, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem cancel_units {S : Type} [CommRing S] {A B C E : Sˣ} {a b : S} (h : A.val * a = B.val * b * C.val)
    (e : B * C = A * E) : a = b * E.val := by
  refine (Units.mul_right_inj A).1 (h.trans ?_)
  rw [mul_right_comm, ← Units.val_mul, e, Units.val_mul, mul_right_comm, _root_.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem fe_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {k : ℕ} (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α)
    (f' : ∀ α, D'.SecB k α)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1)
    (hf : ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
      (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p)
          ((f (hD.xe x)).f p) = (∏ κ, gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))
    (mu α : D'.X) {T' : Over (Spec (CommRingCat.of R'))} (σ : T' ⟶ TK R') (x : T' ⟶ D'.P.A) {y : T'.left} {J'}
    (hJ' : Good D'.P.L y J') :
    sval (f' (α + k • mu)) x.left y J' = sval (f' α) (x * cP D' T' mu).left y J' *
      (feUnit D' k mu α x y J' (fun χ => val (D'.psi χ) σ.left y J') (val D'.rigK σ.left y J')).val := by
  choose J hJ₀ using fun χ : T'.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (T'.hom ≫ spMap φ)
  have hσ : σ.left ≫ jK R' = T'.hom := Over.w σ
  have hκ : (σ.left ≫ hD.g) ≫ hD.W.ι = T'.hom ≫ spMap φ := by
    rw [Category.assoc, hD.g_comm, ← Category.assoc, hσ]
  let κ : T ⟶ TW hD.W := Over.homMk (σ.left ≫ hD.g) hκ
  let β : (T' ⟶ D'.P.A) →* (T ⟶ D.P.A) := pushHom gp T'
  have βl : ∀ x, (β x).left = x.left ≫ Φ := fun _ => rfl
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c χ).left) ≫ Φ = (T'.hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T'.left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : T' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := T') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) (σ.left ≫ hD.g) y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) σ.left y J' :=
    fun χ => by
      have a₁ : σ.left ≫ D'.xK χ = (cP D' T' χ).left := congrArg (fun q => q.left) (comp_cP D' σ χ)
      rw [val_psiW hD σ.left hJ hJ' χ, a₁]
  have vρ : val (D.rigW hD.W) (σ.left ≫ hD.g) y J = Ω 1 * val D'.rigK σ.left y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : (T'.hom ≫ specOf φ) ≫ eSec D.P.A = (1 : T' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one β).symm
    have e := pm _ T'.hom y (fun _ => J ((1 : T' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : T' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : (σ.left ≫ hD.g) ≫ (toUnit (TW hD.W)).left = T'.hom ≫ specOf φ := hκ
    have b₂ : σ.left ≫ (toUnit (TK R')).left = T'.hom := hσ
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have vf : ∀ χ (x : T' ⟶ D'.P.A), sval (f (hD.xe χ)) (x.left ≫ Φ) y J =
      (Ω x ^ ((k : ℤ) - 1) * Ω (cP D' T' χ * x) * (Ω (cP D' T' χ))⁻¹ * Ω 1).val * sval (f' χ) x.left y J' := fun χ x => by
    have c : ∀ i, (x.left ≫ Φ) ≫ D.famφB (hD.xe χ) i = (x.left ≫ D'.famφB χ i) ≫ Φ := fun i => by
      refine (comp_famφB D (β x) (hD.xe χ) i).trans ?_
      rw [comp_famφB, ← βl, ← βc, ← map_mul, ← map_one β]
      fin_cases i <;> rfl
    rw [sval_of _ _ y J (fun i => J ((x.left ≫ D'.famφB χ i) ≫ Φ)) (fun i => congrArg J (c i))]
    refine (hf χ _ x.left y _ (fun i => J' (x.left ≫ D'.famφB χ i)) (fun i => hJ ((x.left ≫ D'.famφB χ i) ≫ Φ))
      (fun i => hJ' (x.left ≫ D'.famφB χ i))).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
    exact prod_famB D' x χ k (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))
  have cN : cubN θ k (β (cP D' T' α)) (β (cP D' T' mu)) (β x) =
      cubN (fun a b c => θ (β a) (β b) (β c)) k (cP D' T' α) (cP D' T' mu) x :=
    Finset.prod_congr rfl fun i _ => by simp only [map_mul, map_pow]
  have key₀ := fe_on hG hD.psiW F f hs (hD.xe mu) (hD.xe α) κ (β x) (z := y) hJ
  rw [← map_nsmul, ← map_add, ← βc, ← map_mul, feUnit, ← βc, ← βc, ← map_add] at key₀
  have key : sval (f (hD.xe (α + k • mu))) (x.left ≫ Φ) y J = sval (f (hD.xe α)) ((x * cP D' T' mu).left ≫ Φ) y J *
      (cubN θ k (β (cP D' T' α)) (β (cP D' T' mu)) (β x) * (θ (β (cP D' T' α)) (β x) (β (cP D' T' mu)))⁻¹ *
        (val (hD.psiW.psi (hD.xe (mu + α))) (σ.left ≫ hD.g) y J * (val (hD.psiW.psi (hD.xe mu)) (σ.left ≫ hD.g) y J)⁻¹ *
          (val (hD.psiW.psi (hD.xe α)) (σ.left ≫ hD.g) y J)⁻¹ * (val (D.rigW hD.W) (σ.left ≫ hD.g) y J)⁻¹ *
          (val (hD.psiW.psi (hD.xe mu)) (σ.left ≫ hD.g) y J ^ k * val (D.rigW hD.W) (σ.left ≫ hD.g) y J ^ k))).val := key₀
  rw [vf, vf, cN, cubN_twist _ _ Ω cub, cub, vψ, vψ, vψ, vρ] at key
  refine cancel_units key ?_
  rw [feUnit, cPoint_add, cPoint_add, cPoint_nsmul, mul_comm (cP D' T' mu) (cP D' T' α), ← _root_.mul_assoc (cP D' T' α),
    mul_comm (cP D' T' mu) x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module

end Pull

end FamPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation in

theorem exists_fam_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α) (f' : ∀ α, D'.SecB k α), (∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) ((f (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))) → ∃ F' : Fam D' (FractionRing R') k, (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) (F'.s α) (D'.famφB α) (DegPre.famε k) (f' α) (DegPre.prB D' (FractionRing R')).left 1) := by
  intro hG R R' _ _ _ _ φ D D' hD k F f f' hs hf
  have ex : ∀ α, ∃ s : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k)),
      GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) s (D'.famφB α) (DegPre.famε k) (f' α)
        (DegPre.prB D' (FractionRing R')).left 1 := fun α => by
    obtain ⟨s, hs⟩ := exists_sec D'.P.isLB (φ' := DegPre.famφ D' (FractionRing R') α) (ε' := DegPre.famε k)
      (fun U _ h => by
        have p := prod_fam D' (FractionRing R') (𝟙 _) α k h
        simp only [Over.id_left, Category.id_comp] at p
        exact (FamPull.prod_famB D' _ α k h).trans p.symm)
      (pullSec D'.P.L _ _ (f' α) (DegPre.prB D' (FractionRing R')).left)
    exact ⟨s, secScal_of_sval D'.P.isLB fun y J hJ => ((hs _ _ y J hJ).trans (sval_pullSec _ _ _ _ _ y hJ)).symm⟩
  choose s hs' using ex
  refine ⟨⟨s, (FamPull.famFE_iff hG s f' hs').2 fun mu α T ρ z J hJ => ?_⟩, hs'⟩
  exact FamPull.fe_pull hG hD F f f' hs hf mu α (Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R') (FractionRing R'))
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))) _ hJ

end GlobalTheory
