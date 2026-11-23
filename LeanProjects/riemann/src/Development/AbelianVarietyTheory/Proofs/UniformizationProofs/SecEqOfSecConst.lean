import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifZero

open GlobalTheory.ToricData

section Const

variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']

theorem gv_one (V : Y.Opens) : gv 1 V = 1 := map_one _

theorem res_eq_one {U V : Y.Opens} (h : V ≤ U) {x : Γ(Y, U)ˣ} (hx : x = 1) : res h x = 1 := by
  rw [hx, map_one]

theorem res_pullU_eq_one (f : Y' ⟶ Y) {U : Y.Opens} {V : Y'.Opens} (h : V ≤ f ⁻¹ᵁ U) {x : Γ(Y, U)ˣ}
    (hx : x = 1) : res h (pullU f U x) = 1 := by
  rw [hx, map_one, map_one]

theorem mul_eq_one_of {M : Type} [Monoid M] {a b : M} (ha : a = 1) (hb : b = 1) : a * b = 1 := by
  rw [ha, hb, _root_.mul_one]

theorem one_isGen_div {X' : Scheme.{0}} (φ : J → (Y ⟶ X)) (ε : J → ℤ) (φ' : J' → (Y ⟶ X')) (ε' : J' → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.div (LB.LinComb (trivLB X) φ ε) (LB.LinComb (trivLB X') φ' ε'))).IsGen := by
  intro i j
  simp only [LB.div, linComb_triv_g, map_one, inv_one, _root_.mul_one]
  exact (res_eq_one _ rfl).trans (mul_eq_one_of rfl (res_eq_one _ rfl)).symm

theorem charUnit_zero (S : Scheme.{0}) (M : Type) [AddCommGroup M] : charUnit S M 0 = 1 := by
  unfold charUnit
  refine res_pullU_eq_one _ _ ?_
  rw [ofAdd_zero, map_one, map_one, map_one]
  rfl

def SecConst {L : LB Y} (s : LB.Sec L) (a : Γ(Y, ⊤)) : Prop := ∀ j, s.f j = resTop (L.U j) a

def cs (φ : J → (Y ⟶ X)) (ε : J → ℤ) (a : Γ(Y, ⊤)) : LB.Sec (LB.LinComb (trivLB X) φ ε) where
  f := fun _ => resTop _ a
  compat := fun i j => by
    rw [linComb_triv_g, Units.val_one, _root_.one_mul, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res]

theorem cs_const (φ : J → (Y ⟶ X)) (ε : J → ℤ) (a : Γ(Y, ⊤)) : SecConst (cs φ ε a) a := fun _ => rfl

theorem map_self {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)) : (Y.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem resTop_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)} (h : resTop V a = resTop V b) : a = b := by
  subst hV
  rwa [resTop, resTop, map_self, map_self] at h

theorem exists_secConst {φ : J → (Y ⟶ X)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (trivLB X) φ ε)) :
    ∃ a, SecConst s a := by
  refine ⟨(Y.presheaf.map (homOfLE (wchart_triv φ (fun _ => PUnit.unit)).ge).op).hom
    (s.f (fun _ => PUnit.unit)), fun j => ?_⟩
  obtain rfl : j = fun _ => PUnit.unit := rfl
  exact ((map_map _ _ _).trans (map_self _ _)).symm

theorem sec_eq_of_secConst {L : LB Y} {s t : LB.Sec L} {a : Γ(Y, ⊤)} (hs : SecConst s a)
    (ht : SecConst t a) : s = t :=
  DVR.SecOps.sec_ext fun j => (hs j).trans (ht j).symm

theorem app_resTop (f : Y' ⟶ Y) (V : Y.Opens) (a : Γ(Y, ⊤)) :
    (f.app V).hom (resTop V a) = resTop (f ⁻¹ᵁ V) (f.appTop.hom a) := app_res' f a V

theorem resTop_mul (V : Y.Opens) (a b : Γ(Y, ⊤)) : resTop V (a * b) = resTop V a * resTop V b :=
  map_mul _ _ _

theorem unit_pow_mul_app (f : Y' ⟶ Y) {U : Y.Opens} {V W : Y'.Opens} (h : W ≤ V) (h' : W ≤ f ⁻¹ᵁ U)
    {u : Γ(Y', V)ˣ} (hu : u = 1) {x : Γ(Y, U)} {a : Γ(Y, ⊤)} (hx : x = resTop U a) (k : ℕ) :
    (res h u).val ^ k * (Y'.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) =
      resTop W (f.appTop.hom a) := by
  rw [hu, hx, map_one, Units.val_one, one_pow, _root_.one_mul, app_resTop, DVR.SecOps.resTop_res]

theorem app_mul_unit (f : Y' ⟶ Y) {U : Y.Opens} {V W : Y'.Opens} (h : W ≤ V) (h' : W ≤ f ⁻¹ᵁ U)
    {u : Γ(Y', V)ˣ} (hu : u = 1) {x : Γ(Y, U)} {a : Γ(Y, ⊤)} (hx : x = resTop U a) :
    (Y'.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) * (res h u).val =
      resTop W (f.appTop.hom a) := by
  rw [hu, hx, map_one, Units.val_one, _root_.mul_one, app_resTop, DVR.SecOps.resTop_res]

theorem secScal_iff {φ₁ : J → (Y' ⟶ X)} {ε₁ : J → ℤ} {s₁ : LB.Sec (LB.LinComb (trivLB X) φ₁ ε₁)}
    {φ₂ : J' → (Y ⟶ X)} {ε₂ : J' → ℤ} {s₂ : LB.Sec (LB.LinComb (trivLB X) φ₂ ε₂)} {a : Γ(Y', ⊤)}
    {b : Γ(Y, ⊤)} (ha : SecConst s₁ a) (hb : SecConst s₂ b) (h : Y' ⟶ Y) (c : Γ(Y', ⊤)) :
    GeneratorPullback.SecScal (trivLB X) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c ↔ h.appTop.hom b = c * a := by
  constructor
  · intro H
    have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
    erw [ha, hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, ← resTop_mul] at this
    exact resTop_inj (top_unique (le_inf (wchart_triv _ _).ge (wchart_triv _ _).ge)) this
  · intro H j₁ j₂ _
    erw [ha, hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, ← resTop_mul, H]

theorem secRel_of {φ₁ : J → (Y' ⟶ X)} {ε₁ : J → ℤ} {s₁ : LB.Sec (LB.LinComb (trivLB X) φ₁ ε₁)}
    {φ₂ : J' → (Y ⟶ X)} {ε₂ : J' → ℤ} {s₂ : LB.Sec (LB.LinComb (trivLB X) φ₂ ε₂)} {a : Γ(Y', ⊤)}
    {b : Γ(Y, ⊤)} (ha : SecConst s₁ a) (hb : SecConst s₂ b) (h : Y' ⟶ Y)
    {φ₃ : J'' → (Y' ⟶ X)} {ε₃ : J'' → ℤ} {u : LB.Gen (LB.LinComb (trivLB X) φ₃ ε₃)}
    (hu : IsConst u 1) (H : a = h.appTop.hom b) :
    GeneratorPullback.SecRel (trivLB X) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u := by
  intro j₁ j₂ j₃ _
  erw [ha, hb, hu, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, H]
  erw [gv_one, Units.val_one, map_one, _root_.mul_one]

variable {A B : Type} [CommRing A] [CommRing B]

theorem appTop_scal (f : Y' ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of A)) (r : A) :
    f.appTop.hom (scal p r) = scal (f ≫ p) r := by
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem scal_specMap (p : Y ⟶ Spec (CommRingCat.of B)) (φ : A →+* B) (r : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  have nat := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [← appTop_scal, scal, scal, nat]

theorem scal_mul (p : Y ⟶ Spec (CommRingCat.of A)) (r s : A) : scal p (r * s) = scal p r * scal p s := by
  simp only [scal, map_mul]

theorem scal_zero (p : Y ⟶ Spec (CommRingCat.of A)) : scal p 0 = 0 := by
  simp only [scal, map_zero]

theorem scal_bijective (p : Y ⟶ Spec (CommRingCat.of A)) [IsIso p] : Function.Bijective (scal p) :=
  (ConcreteCategory.bijective_of_isIso (p.app ⊤)).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)

end Const

variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)

def zeroData : DegData R I where
  toPre := toricPre R PUnit (fun _ => 1)
  psi_even := psiEven _ fun _ => rfl
  tau_bimult := tauBimult _ fun _ _ _ => by simp [polar]
  psi_pos := fun _ h => (h rfl).elim
  psi_tendsto := fun _ => @Set.toFinite _ _ (@Subtype.finite _ (inferInstanceAs (Finite PUnit)) _)

def isTerminalPullback {S S' : Scheme.{0}} (f : S' ⟶ S) :
    IsTerminal ((Over.pullback f).obj (𝟙_ (Over S))) :=
  IsTerminal.isTerminalObj _ _ isTerminalTensorUnit

def zeroGt (e : ℕ) : GtCoord I (zeroData R I).toPre e (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  q := 𝟙 _
  q_hom := (inferInstance : IsMonHom (𝟙 (thickObj R I e (𝟙_ _))))
  q_flat := (inferInstance : Flat (𝟙 (thickObj R I e (𝟙_ _)).left))
  q_surj := (inferInstance : Surjective (𝟙 (thickObj R I e (𝟙_ _)).left))
  q_affine := (inferInstance : IsAffineHom (𝟙 (thickObj R I e (𝟙_ _)).left))
  i := toUnit _ ≫ η
  i_hom := inferInstance
  isKernel := by
    have : IsIso (toUnit (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (zeroData R I).toPre.X)) :=
      isIso_toUnit_splitTorus_punit _
    exact @IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ this
      (inferInstance : IsIso (𝟙 (thickObj R I e (𝟙_ _)))) ⟨Category.comp_id _⟩
  t := fun _ => cg _ _ 1
  t_gen := fun _ => cg_isGen _ _ 1
  t_mul := fun _ _ => corr_of_isConst
    ((isConst_mulGen (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))))
    (isConst_mulGen (cg_isConst _ _ 1) (cg_isConst _ _ 1))
  t_unit := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    (isConst_oneGen _)
  t_weight := fun χ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    ((isConst_mulGen (a := 1) (fun j => by
        obtain rfl : χ = 0 := rfl
        exact (res_pullU_eq_one _ _ (charUnit_zero _ _)).trans (gv_one _).symm)
      ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))

theorem zeroGt_pG (e : ℕ) :
    (zeroGt R I e).pG.left = pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) :=
  Category.id_comp _

def zeroPre : UnifPre I (zeroData R I) (zeroPolAV (Spec (CommRingCat.of (FractionRing R))))
    (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  smooth := (inferInstance : Smooth (𝟙 (Spec (CommRingCat.of R))))
  separated := (inferInstance : IsSeparated (𝟙 (Spec (CommRingCat.of R))))
  gen := (isTerminalPullback (jK R)).uniqueUpToIso isTerminalTensorUnit
  gen_hom := ⟨toUnit_unique _ _, toUnit_unique _ _⟩
  LG := ⟨trivLB _, (zeroData R I).toPre.rig, trivLB_isLB _, (zeroData R I).toPre.rig_gen⟩
  cubG := (zeroData R I).toPre.cub
  symG := (zeroData R I).toPre.sym
  symG_gen := (zeroData R I).toPre.sym_gen
  symG_rig := (zeroData R I).toPre.sym_rig
  ext := ⟨_, one_isGen_div _ _ _ _⟩
  gt := zeroGt R I
  gt_q := fun e => by
    rw [zeroGt_pG, zeroGt_pG]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  gt_t := fun _ _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    (cg_isConst _ _ 1)
  w := fun _ => ⟨fun _ => 1⟩
  w_gen := fun _ => one_isGen_div _ _ _ _
  w_rig := fun e p V h₁ h₂ h₃ =>
    (mul_eq_one_of (res_pullU_eq_one _ h₁ rfl) (res_pullU_eq_one _ h₂ (gv_one _))).trans
      (res_pullU_eq_one _ h₃ (gv_one _)).symm
  w_even := fun e jS jT _ _ V h₁ h₂ h₃ h₄ =>
    (mul_eq_one_of (res_pullU_eq_one _ h₁ (gv_one _)) (res_eq_one h₂ rfl)).trans
      (mul_eq_one_of (res_pullU_eq_one _ h₃ rfl) (res_pullU_eq_one _ h₄ (gv_one _))).symm
  w_cub := fun e T x jL jM _ _ V hB hG hw =>
    (res_pullU_eq_one _ hB (gv_one _)).trans
      (mul_eq_one_of (Finset.prod_eq_one fun k _ =>
        (congrArg (· ^ thε k) (res_pullU_eq_one _ (hw k) rfl)).trans (one_zpow _))
        (res_pullU_eq_one _ hG (gv_one _))).symm
  w_compat := fun e p V h₁ h₂ => (res_pullU_eq_one _ h₁ rfl).trans (res_eq_one h₂ rfl).symm

variable {R I}

theorem expandsAt_iff (e k : ℕ)
    {σ : LB.Sec (LB.LinComb (zeroPre R I).LG.L (K := Fin 1)
      (fun _ => 𝟙 (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (fun _ => (k : ℤ)))}
    {f : ∀ α : (zeroData R I).toPre.X, (zeroData R I).toPre.SecB k α} {a b : R}
    (ha : SecConst σ (scal (𝟙 _) a)) (hb : SecConst (f PUnit.unit) (scal (𝟙 _) b)) :
    (zeroPre R I).ExpandsAt e k σ f ↔ a - b ∈ I ^ (e + 1) := by
  let p := pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e)
  let q := pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e)
  haveI : IsIso q := (inferInstance : IsIso (pullback.snd (𝟙 _) (thick R I e)))
  have hp : ∀ x : R, scal p x = scal q (Ideal.Quotient.mk _ x) := fun x => by
    rw [← scal_specMap]
    exact congrArg (scal · x) ((Category.comp_id _).symm.trans pullback.condition)
  have hG : ∀ x : R, (fstG I e (𝟙_ _)).left.appTop.hom (scal (𝟙 _) x) = scal p x := fun x =>
    (appTop_scal _ _ _).trans (congrArg (scal · x) (Category.comp_id _))
  have hB : ∀ x : R, ((zeroPre R I).gt e).pG.left.appTop.hom (scal (𝟙 _) x) = scal p x := fun x =>
    (appTop_scal _ _ _).trans (congrArg (scal · x) ((Category.comp_id _).trans (zeroGt_pG R I e)))
  rw [← Ideal.Quotient.eq, ← (scal_bijective q).1.eq_iff, ← hp, ← hp]
  have hpre : ∀ {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {U : Y.Opens}, U = ⊤ → ⊤ ≤ g ⁻¹ᵁ U := by
    rintro _ _ g _ rfl
    exact le_rfl
  have key : ∀ S p' j₁ jf jt, (zeroPre R I).expW e p' j₁ S jf jt = ⊤ := fun S p' j₁ jf jt =>
    top_unique (le_inf (le_inf (le_inf (wchart_triv _ _).ge (wchart_triv _ _).ge)
      (hpre _ (wchart_triv _ _))) (Finset.le_inf fun α _ =>
        le_inf (hpre _ (wchart_triv _ _)) (wchart_triv _ _).ge))
  constructor
  · rintro ⟨S, h0, h⟩
    have h1 := h (fun _ => PUnit.unit, fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ => PUnit.unit)
      (fun _ _ => PUnit.unit) rfl (fun _ _ _ => @Subsingleton.elim PUnit _ _ _)
    have h2 := ((unit_pow_mul_app _ _ _ rfl (ha _) k).symm.trans h1).trans
      (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _))
    rw [hG, hB, Finset.sum_const, Finset.card_attach] at h2
    by_cases hS : PUnit.unit ∈ S
    · obtain rfl : S = {PUnit.unit} := Finset.eq_singleton_iff_unique_mem.2 ⟨hS, fun _ _ => rfl⟩
      exact resTop_inj (key _ _ _ _ _) (h2.trans (one_nsmul _))
    · obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun _ => hS
      rw [Finset.card_empty, zero_smul] at h2
      have h3 := ((app_resTop _ _ _).symm.trans
        (congrArg _ (hb (fun _ => PUnit.unit)).symm)).trans (h0 PUnit.unit hS _)
      rw [hB] at h3
      exact (resTop_inj (key _ _ _ _ _) (h2.trans (map_zero _).symm)).trans
        (resTop_inj (top_unique (hpre _ (wchart_triv _ _))) (h3.trans (map_zero _).symm)).symm
  · intro H
    refine ⟨{PUnit.unit}, fun α hα => (hα (Finset.mem_singleton_self _)).elim, ?_⟩
    intro p' j₁ jf jt _ _
    refine (unit_pow_mul_app _ _ _ rfl (ha _) k).trans
      (Eq.trans ?_ (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _)).symm)
    rw [hG, hB, Finset.sum_const, Finset.card_attach, H]
    exact (one_nsmul _).symm

abbrev pGK : pullback (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (jK R) ⟶
    Spec (CommRingCat.of (FractionRing R)) := pullback.snd _ _

abbrev pBK : (DegPre.BF (zeroData R I).toPre (FractionRing R)).left ⟶
    Spec (CommRingCat.of (FractionRing R)) := (fst (TF (R := R) (FractionRing R)) _).left

instance : IsIso (pGK (R := R)) := (inferInstance : IsIso (pullback.snd (𝟙 _) (jK R)))

instance : IsIso (pBK (R := R) (I := I)) :=
  (inferInstance : IsIso (pullback.fst (TF (R := R) (FractionRing R)).hom (𝟙 _)))

theorem expands_iff [IsHausdorff I R] (k : ℕ) {s : (zeroPre R I).SecK k}
    {F : Fam (zeroData R I).toPre (FractionRing R) k} {x y : FractionRing R}
    (hs : SecConst s (scal pGK x)) (hF : SecConst (F.s PUnit.unit) (scal pBK y)) :
    (zeroPre R I).Expands k s F ↔ x = y := by
  have e1 : ∀ a r : R, (pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (jK R)).appTop.hom (scal (𝟙 _) a) =
      scal (pGK ≫ jK R) r * scal pGK x ↔ algebraMap R _ a = algebraMap R _ r * x := fun a r => by
    rw [← (scal_bijective pGK).1.eq_iff, scal_mul, ← scal_specMap, ← scal_specMap]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a) pullback.condition))
  have hB : ∀ a : R, scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom a =
      scal pBK (algebraMap R (FractionRing R) a) := fun a => by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) _)]
    exact (congrArg (scal · a) (Category.assoc _ _ _).symm).trans
      ((scal_specMap _ _ _).trans (scal_specMap _ _ _))
  have e2 : ∀ a r : R, (DegPre.prB (zeroData R I).toPre (FractionRing R)).left.appTop.hom (scal (𝟙 _) a) =
      scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom r * scal pBK y ↔
      algebraMap R _ a = algebraMap R _ r * y := fun a r => by
    rw [← (scal_bijective (pBK (I := I))).1.eq_iff, scal_mul, ← hB, ← hB]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a)
      (Over.w (DegPre.prB (zeroData R I).toPre (FractionRing R)))))
  constructor
  · rintro ⟨r, hr, σ, f, h1, h2, h3⟩
    obtain ⟨a', ha⟩ := exists_secConst σ
    obtain ⟨a, rfl⟩ := (scal_bijective (𝟙 (Spec (CommRingCat.of R)))).2 a'
    obtain ⟨b', hb⟩ := exists_secConst (f PUnit.unit)
    obtain ⟨b, rfl⟩ := (scal_bijective (𝟙 (Spec (CommRingCat.of R)))).2 b'
    have hab : a = b := by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus' (I := I) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) ((expandsAt_iff n k ha hb).1 (h3 n))
    have hx := (e1 a r).1 ((secScal_iff hs ha _ _).1 h1)
    have hy := (e2 b r).1 ((secScal_iff hF hb _ _).1 (h2 PUnit.unit))
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
      (hx.symm.trans (hab ▸ hy))
  · rintro rfl
    obtain ⟨⟨a, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
    have h' : algebraMap R (FractionRing R) a = algebraMap R _ r * x := h.symm.trans (mul_comm _ _)
    exact ⟨r, nonZeroDivisors.ne_zero r.2, cs _ _ (scal (𝟙 _) a), fun _ => cs _ _ (scal (𝟙 _) a),
      (secScal_iff hs (cs_const _ _ _) _ _).2 ((e1 a r).2 h'),
      fun _ => (secScal_iff hF (cs_const _ _ _) _ _).2 ((e2 a r).2 h'),
      fun e => (expandsAt_iff e k (cs_const _ _ _) (cs_const _ _ _)).2 (by rw [sub_self]; exact zero_mem _)⟩

def constFam (k : ℕ) (c : Γ((DegPre.BF (zeroData R I).toPre (FractionRing R)).left, ⊤)) :
    Fam (zeroData R I).toPre (FractionRing R) k where
  s := fun _ => cs _ _ c
  fe := fun mu α u _ hu => by
    have hz : IsIso (DegPre.zF (zeroData R I).toPre (FractionRing R)).left := by
      have : (DegPre.zF (zeroData R I).toPre (FractionRing R)).left ≫ pBK = 𝟙 _ :=
        congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) (FractionRing R)))
          (toUnit _ ≫ η[(zeroData R I).toPre.P.A]))
      exact IsIso.of_isIso_fac_right this
    have ht : DegPre.trF (zeroData R I).toPre (FractionRing R) mu = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm)
        (toUnit_unique _ _)
    have hm : IsConst (DegPre.famMult (zeroData R I).toPre (FractionRing R) k mu α) 1 :=
      (isConst_pullGen (isConst_mulGen (isConst_mulGen (isConst_powGen (psi_isConst _ mu) k)
        (tau_isConst _ mu α)) (isConst_powGen (rigK_isConst _) k)) _).of_eq (by
          simp only [polar, inv_one, _root_.mul_one, unitOn_one, one_pow, map_one])
    obtain ⟨v, hv⟩ := exists_isConst u
    have hv1 : v = 1 := pullTop_injective (DegPre.zF (zeroData R I).toPre (FractionRing R)).left
      ((eq_of_corr (isConst_pullGen hv _) hm hu).trans (map_one _).symm)
    refine secRel_of (cs_const _ _ _) (cs_const _ _ _) _ (hv.of_eq hv1) ?_
    rw [ht, Over.id_left, Scheme.Hom.id_appTop]
    rfl

theorem expBij [IsHausdorff I R] (k : ℕ) : (zeroPre R I).ExpBij k := by
  have hS : ∀ s : (zeroPre R I).SecK k, ∃ x, SecConst s (scal pGK x) := fun s => by
    obtain ⟨a, ha⟩ := exists_secConst s
    obtain ⟨x, rfl⟩ := (scal_bijective (pGK (R := R))).2 a
    exact ⟨x, ha⟩
  have hF : ∀ F : Fam (zeroData R I).toPre (FractionRing R) k,
      ∃ y, SecConst (F.s PUnit.unit) (scal pBK y) := fun F => by
    obtain ⟨a, ha⟩ := exists_secConst (F.s PUnit.unit)
    obtain ⟨y, rfl⟩ := (scal_bijective (pBK (R := R) (I := I))).2 a
    exact ⟨y, ha⟩
  constructor
  · intro s
    obtain ⟨x, hx⟩ := hS s
    refine ⟨constFam k (scal pBK x), (expands_iff k hx (cs_const _ _ _)).2 rfl, fun F h => ?_⟩
    obtain ⟨y, hy⟩ := hF F
    obtain rfl := (expands_iff k hx hy).1 h
    exact DVR.fam_ext fun _ j => hy j
  · intro F
    obtain ⟨y, hy⟩ := hF F
    refine ⟨cs _ _ (scal pGK y), (expands_iff k (cs_const _ _ _) hy).2 rfl, fun s h => ?_⟩
    obtain ⟨x, hx⟩ := hS s
    obtain rfl := (expands_iff k hx hy).1 h
    exact sec_eq_of_secConst hx (cs_const _ _ _)

end GlobalTheory.UnifZero
