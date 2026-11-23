import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.TorsionExt

open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar

theorem isoRelM_pull {Y Y' Y'' X₁ X₂ Z Z' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z ⟶ X₁} {h : Y' ⟶ Z} {g₂ : Y' ⟶ X₂}
    {S S' : Type} [CommRing S] [CommRing S'] {f : S →+* S'}
    {π : Z ⟶ Spec (CommRingCat.of S)} {π' : Z' ⟶ Spec (CommRingCat.of S')}
    {ϖ : Y' ⟶ Spec (CommRingCat.of S)} {ϖ' : Y'' ⟶ Spec (CommRingCat.of S')}
    {a : SecOver π (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : SecOver ϖ (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h a g₂ (𝟙 _) b) {q : Z' ⟶ Z} {n : Y'' ⟶ Y'}
    (hq : q ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) (hn : n ≫ ϖ = ϖ' ≫ Spec.map (CommRingCat.ofHom f))
    {g₁' : Z' ⟶ X₁} {g₂' : Y'' ⟶ X₂} (e₁ : ∀ _ : Fin 1, g₁' = q ≫ g₁) (e₂ : ∀ _ : Fin 1, g₂' = n ≫ g₂)
    {m' : Y'' ⟶ Y} (hm : n ≫ m = m') {h' : Y'' ⟶ Z'} (hh : h' ≫ q = n ≫ h) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m' k g₁' h'
      (pullOver L₁ (fun _ => (k : ℤ)) (φ := fun _ : Fin 1 => g₁) (φ' := fun _ => g₁') hq e₁ a) g₂' (𝟙 _)
      (pullOver L₂ (fun _ => (k : ℤ)) (φ := fun _ : Fin 1 => g₂) (φ' := fun _ => g₂') hn e₂ b) := by
  subst hm
  have c₁ : h' ≫ g₁' = (n ≫ m) ≫ f₁ := by rw [e₁ 0, ← Category.assoc, hh, Category.assoc, H.1, Category.assoc]
  have c₂ : 𝟙 _ ≫ g₂' = (n ≫ m) ≫ f₂ := by
    rw [e₂ 0, Category.id_comp, Category.assoc, ← H.2.1, Category.id_comp]
  refine (isoRelM_iff w _ k _ c₁ _ c₂ _ _).2 fun y i₂ i₁ h₂ h₁ => ?_
  have K := (isoRelM_iff w _ k _ H.1 _ H.2.1 _ _).1 H _ (𝟙 _ ≫ n) y i₂ i₁ h₂ h₁
  rw [Category.comp_id, Category.assoc, Category.assoc, ← hh, ← Category.assoc _ h'] at K
  rw [Category.comp_id]
  refine (gs_pullFn hn _ _ _ y (mem_wchart.2 fun _ => ?_)).trans (K.trans (congrArg _ ?_))
  · exact (congrArg (fun q : _ ⟶ X₂ => q y ∈ L₂.U i₂) c₂).mpr h₂
  · refine Eq.symm (gs_pullFn hq _ _ _ y (mem_wchart.2 fun _ => ?_))
    exact (congrArg (fun q : _ ⟶ X₁ => q y ∈ L₁.U i₁) c₁).mpr h₁

theorem proportional_iff {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) (f g : V →ₗ[K] V)
    (f' g' : W →ₗ[F] W) (hf : ∀ v, f' (a v) = a (f v)) (hg : ∀ v, g' (a v) = a (g v)) :
    (∃ c : K, c ≠ 0 ∧ ∀ v, f v = c • g v) ↔ ∃ c : F, c ≠ 0 ∧ ∀ v, f' v = c • g' v := by
  constructor
  · rintro ⟨c, hc, H⟩
    refine ⟨algebraMap K F c, (map_ne_zero _).2 hc, fun v => ?_⟩
    have e : f' = algebraMap K F c • g' := LinearMap.ext_on h.span (by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.smul_apply, hf, hg, H, map_smulₛₗ])
    rw [e]; rfl
  · rintro ⟨c, hc, H⟩
    obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap K F).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap K F).injective)
    have h1 : ℓ 1 = 1 := by simpa using LinearMap.congr_fun hℓ 1
    obtain ⟨Λ, hΛ⟩ := h.coord ℓ
    have h2 : ∀ v, Λ (a v) = v := fun v => by
      have := hΛ 1 v
      rwa [one_smul, h1, one_smul] at this
    have h3 : ∀ v, f v = ℓ c • g v := fun v => by
      rw [← hΛ c, ← hg, ← H, hf, h2]
    by_cases h0 : ℓ c = 0
    · refine ⟨1, one_ne_zero, fun v => ?_⟩
      have h4 : f v = 0 := by rw [h3, h0, zero_smul]
      have h5 : a (g v) = 0 := by
        have := H (a v)
        rw [hf, hg, h4, map_zero] at this
        exact (smul_eq_zero.1 this.symm).resolve_left hc
      rw [h4, ← h2 (g v), h5, map_zero, smul_zero]
    · exact ⟨ℓ c, h0, h3⟩

variable {R : Type} [CommRing R] [IsDomain R]

section OneField

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable (A F k) in

abbrev AbSec : Type := SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

theorem actVal_unique {θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)} {t u u' : AbSec A F k}
    (h : ActVal θ t u) (h' : ActVal θ t u') : u = u' :=
  sec_ext' A.isLB fun y J hJ => (h _ _ y J hJ).trans (h' _ _ y J hJ).symm

theorem translT_base (x : TFK (R := R) F ⟶ A.A) : (translT A.A x).left ≫ abelianBase A F = abelianBase A F :=
  congrArg (fun q => q.left) (lift_fst _ _ : translT A.A x ≫ fst _ _ = _)

theorem exists_act (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ Θ : AbSec A F k →ₗ[F] AbSec A F k, ∀ t, ActVal θ t (Θ t) := by
  choose Θ hΘ using exists_actVal A.isLB θ
  refine ⟨⟨⟨Θ, fun s s' => actVal_unique (hΘ _) fun Z r z J hJ => ?_⟩,
    fun c s => actVal_unique (hΘ _) fun Z r z J hJ => ?_⟩, hΘ⟩
  · refine (sval_add' hJ r _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm)
    exact (congrArg₂ (· + ·) (hΘ s Z r z J hJ) (hΘ s' Z r z J hJ)).trans (mul_add _ _ _).symm
  · refine (sval_smul' hJ r _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm)
    rw [Category.assoc, translT_base]
    exact (congrArg _ (hΘ s Z r z J hJ)).trans (mul_left_comm _ _ _)

theorem exists_act_smul (hG : GlobalFnsSt) (θ θ' : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (h : θ'.pt = θ.pt) :
    ∃ c : F, c ≠ 0 ∧ ∀ t u u' : AbSec A F k, ActVal θ t u → ActVal θ' t u' → u' = c • u := by
  obtain ⟨x, φ, hφ⟩ := θ
  obtain ⟨x', φ', hφ'⟩ := θ'
  obtain rfl : x' = x := h
  obtain ⟨a, ha⟩ := WeilMul.exists_ratio A.isLB (K := Fin 2)
    (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x').left]) (ε := ![(k : ℤ), -(k : ℤ)])
    (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _) hφ' hφ
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' h h' => sec_ext' A.isLB fun y J hJ => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 (TFK (R := R) F)) (1 : _ ⟶ A.A)).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · refine (h' _ _ y J hJ).trans (Eq.trans ?_ (sval_smul' hJ _ c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (ha _ (𝟙 _) y J hJ) (h _ _ y J hJ).symm)
    rw [← _root_.mul_assoc, ← Units.val_mul]
    exact congrArg₂ (· * ·) (congrArg Units.val (inv_mul_cancel_right _ _).symm) rfl

theorem qkToAk_iff (hG : GlobalFnsSt) {D : DegPre R} {p : QkPt D F k}
    {E : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) → Fam D F k → Prop} (e : AbSec A F k ≃ₗ[F] Fam D F k)
    (he : ∀ t s, E t s ↔ e t = s) {θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)}
    {Θ : AbSec A F k →ₗ[F] AbSec A F k} (hΘ : ∀ t, ActVal θ t (Θ t)) {w : Frm D F k p.g.b} (hw : w.IsGen)
    {Φ : Fam D F k →ₗ[F] Fam D F k} (hΦ : ∀ s, PhiVal p w s.s (Φ s).s) (hx : θ.pt ^ k = 1) :
    QkToAk D F A k E p θ.pt ↔
      ∃ c : F, c ≠ 0 ∧ ∀ s, (e.toLinearMap ∘ₗ Θ ∘ₗ e.symm.toLinearMap) s = c • Φ s := by
  constructor
  · rintro ⟨-, H⟩
    obtain ⟨w₁, hw₁, H⟩ := H θ rfl
    obtain ⟨c, hc, hcs⟩ := TorsionImage.exists_smul_of_phiVal p w w₁ hw hw₁
    exact ⟨c, hc, fun s => hcs s _ _ (hΦ s) ((phiRel_iff hG p w₁ hw₁ _ _).1
      (H (e.symm s) (Θ (e.symm s)) s _ ((he _ _).2 (e.apply_symm_apply s)) ((he _ _).2 rfl)
        ((hΘ _).isActOf A.isLB)))⟩
  · rintro ⟨c, hc, H⟩
    refine ⟨hx, fun θ' hθ' => ?_⟩
    obtain ⟨a, ha, has⟩ := exists_act_smul hG θ θ' hθ'
    obtain ⟨w', hw', h⟩ := ProdTorsion.exists_phiRel_smul hG p w hw (a * c) (mul_ne_zero ha hc)
    refine ⟨w', hw', fun t t' s s' h₁ h₂ h₃ => ?_⟩
    obtain rfl := (he _ _).1 h₁
    obtain rfl := (he _ _).1 h₂
    obtain rfl := has t _ t' (hΘ t) (ThetaBaseChange.actVal_of_isActOf h₃)
    have e₁ : e (Θ t) = c • Φ (e t) := (congrArg (fun v => e (Θ v)) (e.symm_apply_apply t)).symm.trans (H (e t))
    have e₂ : e (a • Θ t) = (a * c) • Φ (e t) := by rw [map_smul, e₁, smul_smul]
    rw [e₂]
    exact h _ _ ((phiRel_iff hG p w hw _ _).2 (hΦ _))

end OneField

section TwoFields

variable (E F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

def fieldMap : TFK (R := R) F ⟶ TFK (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (specMap_jFK E F)

theorem whisker_fst (Y : Over (TK R).left) : (fieldMap (R := R) E F ▷ Y).left ≫ (fst (TFK (R := R) E) Y).left =
    (fst (TFK (R := R) F) Y).left ≫ Spec.map (CommRingCat.ofHom (algebraMap E F)) :=
  congrArg (fun q => q.left) (whiskerRight_fst (fieldMap (R := R) E F) Y)

theorem whisker_snd (Y : Over (TK R).left) :
    (fieldMap (R := R) E F ▷ Y).left ≫ (snd (TFK (R := R) E) Y).left = (snd (TFK (R := R) F) Y).left :=
  congrArg (fun q => q.left) (whiskerRight_snd (fieldMap (R := R) E F) Y)

def abPull (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) :
    AbSec A E k →ₛₗ[algebraMap E F] AbSec A F k :=
  pullOver A.L (K := Fin 1) (fun _ => (k : ℤ)) (φ := fun _ => (snd (TFK (R := R) E) A.A).left)
    (φ' := fun _ => (snd (TFK (R := R) F) A.A).left) (whisker_fst E F A.A) (fun _ => (whisker_snd E F A.A).symm)

variable {E F}

theorem actVal_pull {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k : ℕ}
    {θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) E)} {θ' : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)}
    (h₁ : θ'.pt = fieldMap E F ≫ θ.pt)
    (h₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) J, Good A.L z J →
      thetaVal θ' r z J = thetaVal θ (r ≫ (fieldMap (R := R) E F ▷ A.A).left) z J)
    {t u : AbSec A E k} (h : ActVal θ t u) : ActVal θ' (abPull E F A k t) (abPull E F A k u) := by
  intro Z r z J hJ
  refine (sval_pullOver _ _ _ _ hJ).trans ((h _ _ z J hJ).trans (congrArg₂ (· * ·)
    (congrArg Units.val (h₂ Z r z J hJ).symm) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm)))
  have e : (translT A.A θ'.pt).left ≫ (fieldMap (R := R) E F ▷ A.A).left =
      (fieldMap (R := R) E F ▷ A.A).left ≫ (translT A.A θ.pt).left := by
    rw [h₁]; exact congrArg (fun q => q.left) (translT_comp (fieldMap (R := R) E F) θ.pt)
  rw [Category.assoc, Category.assoc, e]
  rfl

theorem exists_phiVal_pull (hG : GlobalFnsSt) {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : w.IsGen) :
    ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧ ∀ s t : Fam D E k, PhiVal p w s.s t.s →
      PhiVal p' w' (famPull D E F hG k s).s (famPull D E F hG k t).s := by
  obtain ⟨hy, hb, hs⟩ := h
  have hb' : p'.g.b = baseMap (R := R) E F ≫ p.g.b := Over.OverMorphism.ext hb
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F p'.g.b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  refine ⟨w', hw', fun s t H α β hβ T ρ z J hJ => ?_⟩
  have e₁ : DegPre.trPt D F p'.g.b ≫ famMap D E F = famMap D E F ≫ DegPre.trPt D E p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D E F)).trans (tr_pr D F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D E _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D E F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) E F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D E k α p.g.b (ρ ≫ famMap D E F) z J = uVal D F k α p'.g.b ρ z J := by
    have : famMap D E F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D E F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, hv _ _ z J hJ, val_pull hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

variable (E F) in

def grpPull (k : ℕ) : GroupSec U E k →ₛₗ[algebraMap E F] GroupSec U F k :=
  pullOver U.LG.L _ (whisker_fst E F ((Over.pullback (jK R)).obj G))
    (fun _ => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (whisker_snd E F _))).symm)

theorem expandsG_pull (hG : GlobalFnsSt) {k : ℕ} {v : GroupSec U E k} {s : Fam D.toPre E k}
    (h : U.ExpandsG E k v s) : U.ExpandsG F k (grpPull E F U k v) (famPull D.toPre E F hG k s) := by
  obtain ⟨n, c, x, hx, e₁, e₂⟩ := (expandsG_iff U E k v s).1 h
  refine (expandsG_iff U F k _ _).2 ⟨n, fun i => algebraMap E F (c i), x, hx, ?_, fun α => ?_⟩
  · rw [e₁, map_sum]
    refine Finset.sum_congr rfl fun i _ => (map_smulₛₗ _ _ _).trans (congrArg _ ?_)
    refine sec_ext' U.LG.isLB fun y J hJ => (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm))
    rw [Category.assoc, whisker_snd]
  · refine (congrArg (termPull D.toPre E F k α) (e₂ α)).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => (map_smulₛₗ _ _ _).trans (congrArg _ ?_)
    refine sec_ext' D.toPre.P.isLB fun y J hJ => (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm))
    have e : famMap D.toPre E F ≫ famMap D.toPre (FractionRing R) E = famMap D.toPre (FractionRing R) F := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, famMap_fst, ← Category.assoc, famMap_fst, famMap_fst, Category.assoc]
        refine congrArg (_ ≫ ·) (Over.OverMorphism.ext ?_)
        exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q))
          (IsScalarTower.algebraMap_eq (FractionRing R) E F).symm)
      · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd _ _ _)).trans
          ((famMap_snd _ _ _).trans (famMap_snd _ _ _).symm))
    rw [Category.assoc, ← Over.comp_left, e]

theorem expandsF_pull (hG : GlobalFnsSt) {k : ℕ} {w : W0 U} {t : AbSec A E k} {s : Fam D.toPre E k}
    (h : U.ExpandsF E k w t s) : U.ExpandsF F k w (abPull E F A k t) (famPull D.toPre E F hG k s) := by
  obtain ⟨v, a, b⟩ := h
  refine ⟨grpPull E F U k v, ?_, expandsG_pull U hG b⟩
  have g : U.genF F ≫ fieldMap (R := R) E F ▷ A.A = fieldMap (R := R) E F ▷ _ ≫ U.genF E := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have g' : (U.genF F).left ≫ (fieldMap (R := R) E F ▷ A.A).left =
      (fieldMap (R := R) E F ▷ (Over.pullback (jK R)).obj G).left ≫ (U.genF E).left := congrArg (fun q => q.left) g
  exact isoRelM_pull a (whisker_fst E F A.A) (whisker_fst E F ((Over.pullback (jK R)).obj G)) _ _
    (whisker_snd E F ((Over.pullback (jK R)).obj G)) g'

end TwoFields

theorem qkToAkU_iff_of_algebra (hG : GlobalFnsSt) (hK : KerPowSt) {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E]
    [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F] {k : ℕ} (hk : 1 ≤ k)
    {p : QkPt D.toPre E k} {p' : QkPt D.toPre F k} (hp : QkExt (algebraMap E F) p p') (x : TFK (R := R) E ⟶ A.A) :
    QkToAkU U.toUnifPre E k p x ↔ QkToAkU U.toUnifPre F k p' (fieldMap E F ≫ x) := by
  refine forall₂_congr fun w₀ hw₀ => ?_
  have hpow : (fieldMap (R := R) E F ≫ x) ^ k = fieldMap (R := R) E F ≫ x ^ k :=
    (map_pow (preHom (fieldMap (R := R) E F)) x k).symm
  by_cases hx : x ^ k = 1
  swap
  · refine iff_of_false (fun h => hx h.1) fun h => hx ?_
    have : Epi (fieldMap (R := R) E F).left := by
      have : Flat (fieldMap (R := R) E F).left := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))))
      have : Surjective (fieldMap (R := R) E F).left :=
        ⟨fun z => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum E) _ _⟩⟩
      have : QuasiCompact (fieldMap (R := R) E F).left :=
        inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap E F))))
      exact Flat.epi_of_flat_of_surjective _
    have e : fieldMap (R := R) E F ≫ x ^ k = fieldMap (R := R) E F ≫ 1 :=
      hpow.symm.trans (h.1.trans (MonObj.comp_one _).symm)
    exact Over.OverMorphism.ext ((cancel_epi (fieldMap (R := R) E F).left).1 (congrArg (fun q => q.left) e))
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hK _ A E _ k hk x hx
  obtain ⟨θ', h₁, h₂⟩ := exists_theta_pull A.isLB (fieldMap (R := R) E F) θ
  obtain ⟨Θ, hΘ⟩ := exists_act θ
  obtain ⟨Θ', hΘ'⟩ := exists_act θ'
  obtain ⟨w, hw⟩ : ∃ w : Frm D.toPre E k p.g.b, w.IsGen := exists_gen_of_local D.toPre.P.L D.toPre.P.isLB _ _
  obtain ⟨w', hw', hww⟩ := exists_phiVal_pull hG hp hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D E k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D F k hk p' w' hw'
  have v := fun s => (phiRel_iff hG p w hw s _).1 ((hΦ s _).2 rfl)
  have v' := fun s => (phiRel_iff hG p' w' hw' s _).1 ((hΦ' s _).2 rfl)
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U E hk w₀ hw₀
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  have c : ∀ t, e' (abPull E F A k t) = famPull D.toPre E F hG k (e t) := fun t =>
    (he' _ _).1 (expandsF_pull U.toUnifPre hG ((he _ _).2 rfl))
  rw [← h₁]
  refine (qkToAk_iff hG e he hΘ hw v hx).trans (Iff.trans ?_
    (qkToAk_iff hG e' he' hΘ' hw' v' (by rw [h₁, hpow, hx, MonObj.comp_one])).symm)
  refine proportional_iff (isExtension_famPull D.toPre E F hG hk) _ _ _ _ (fun s => ?_)
    (fun s => phi_unique p' w' (v' _) (hww _ _ (v s)))
  obtain ⟨t, rfl⟩ := e.surjective s
  show e' (Θ' (e'.symm _)) = famPull D.toPre E F hG k (e (Θ (e.symm _)))
  rw [← c, ← c, e.symm_apply_apply, e'.symm_apply_apply]
  exact congrArg e' (actVal_unique (hΘ' _) (actVal_pull h₁ h₂ (hΘ t)))

theorem qkToAkU_iff_of_qkExt : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' → x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x') := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ F' _ _ _ σ k hk p p' x x' hp hx
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  obtain rfl : x' = fieldMap F F' ≫ x := Over.OverMorphism.ext hx
  exact qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hk hp x

end GlobalTheory.TorsionExt
