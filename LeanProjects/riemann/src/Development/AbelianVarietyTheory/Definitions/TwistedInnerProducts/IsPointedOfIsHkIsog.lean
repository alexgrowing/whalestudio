import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTrace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

section Kernel

variable {A} {T : Over S}

theorem translT_mul (a b : T ⟶ A) : translT A (a * b) = translT A b ≫ translT A a := by
  have h := lift_transl (fst T A) (translPt A b) a
  rw [translT, translT, translT] at *
  rw [h, translPt_eq, translPt_eq, MonObj.comp_mul, _root_.mul_assoc]

theorem translT_one : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

variable (A) in

def transKer {Z : Scheme.{0}} (Ψ : (T ⊗ A).left ⟶ Z) : Subgroup (T ⟶ A) where
  carrier := {c | (translT A c).left ≫ Ψ = Ψ}
  one_mem' := by
    show _ ≫ Ψ = Ψ
    rw [translT_one]
    exact Category.id_comp _
  mul_mem' := fun {a b} (ha : _ ≫ Ψ = Ψ) (hb : _ ≫ Ψ = Ψ) => by
    show _ ≫ Ψ = Ψ
    rw [translT_mul, Over.comp_left, Category.assoc, ha, hb]
  inv_mem' := fun {a} (ha : _ ≫ Ψ = Ψ) => by
    show _ ≫ Ψ = Ψ
    conv_lhs => rw [← ha]
    rw [← Category.assoc, ← Over.comp_left, ← translT_mul, mul_inv_cancel, translT_one]
    exact Category.id_comp _

theorem mem_transKer {Z : Scheme.{0}} {Ψ : (T ⊗ A).left ⟶ Z} {c : T ⟶ A} :
    c ∈ transKer A Ψ ↔ (translT A c).left ≫ Ψ = Ψ := Iff.rfl

end Kernel

def IsRepsModTors {G : Type} [Group G] (C : Subgroup G) (p : ℕ) {n : ℕ} (r : Fin n → G) : Prop :=
  (∀ i, r i ∈ C) ∧ ∀ c ∈ C, ∃! i, (c * (r i)⁻¹) ^ p = 1

variable (L : RigLB A) {Y : Scheme.{0}} {x x' : Y ⟶ S}
  (Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left) (k : ℤ)

abbrev isoφ : Fin 2 → ((Over.mk x ⊗ A).left ⟶ A.left) :=
  ![(snd (Over.mk x) A).left, Ψ ≫ (snd (Over.mk x') A).left]

abbrev isoLB : LB (Over.mk x ⊗ A).left := LB.LinComb L.L (isoφ A Ψ) ![k, -1]

def IsPointed : Prop :=
  Ψ ≫ (fst (Over.mk x') A).left = (fst (Over.mk x) A).left ∧
    (ptSecT A (1 : Over.mk x ⟶ A)).left ≫ Ψ = (ptSecT A (1 : Over.mk x' ⟶ A)).left

def IsRigIso (β : LB.Gen (isoLB A L Ψ k)) : Prop :=
  IsPointed A Ψ ∧ β.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ β (ptSecT A (1 : Over.mk x ⟶ A)).left)
      (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))

def IsCarried (β : LB.Gen (isoLB A L Ψ k)) (s' : LB.Sec (LPow A L.L 1 (Over.mk x')))
    (t : LB.Sec (LPow A L.L k (Over.mk x))) : Prop :=
  GeneratorPullback.SecRel L.L (fun _ : Fin 1 => (snd (Over.mk x) A).left) (fun _ => k) t
    (fun _ : Fin 1 => (snd (Over.mk x') A).left) (fun _ => 1) s' Ψ (isoφ A Ψ) ![k, -1] β

def IsDescLift (β : LB.Gen (isoLB A L Ψ k)) (U : ThetaGrp A L.L k (Over.mk x)) : Prop :=
  U.pt ∈ transKer A Ψ ∧
    LB.Gen.Corr L.L _ _ _ _ U.φ
      (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (translT A U.pt).left)))

def IsMulPull (N : ℕ) {T : Over S} (s : LB.Sec (LPow A L.L 1 T)) (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁

def IsThetaTrace (p : ℕ) (s : LB.Sec (LPow A L.L 1 (Over.mk x))) (s' : LB.Sec (LPow A L.L 1 (Over.mk x'))) : Prop :=
  ∃ (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (s₁ t : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x)))
    (n : ℕ) (U : Fin n → ThetaGrp A L.L ((p : ℤ) ^ 2) (Over.mk x))
    (F : Fin n → LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))),
    IsRigIso A L Ψ _ β ∧ IsMulPull A L p s s₁ ∧ IsCarried A L Ψ _ β s' t ∧
    IsRepsModTors (transKer A Ψ) p (fun i => (U i).pt) ∧ (∀ i, IsDescLift A L Ψ _ β (U i)) ∧
    (∀ i, IsActOf A L.L _ (U i) s₁ (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

def IsThetaTraceSym [IsCommMonObj A] (p : ℕ) (s : LB.Sec (LPow A L.L 1 (Over.mk x)))
    (s' : LB.Sec (LPow A L.L 1 (Over.mk x'))) : Prop :=
  ∃ (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (t : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x)))
    (n : ℕ) (r : Fin n → (Over.mk x ⟶ A)) (F : Fin n → LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))),
    IsRigIso A L Ψ _ β ∧ IsCarried A L Ψ _ β s' t ∧ IsRepsModTors (transKer A Ψ) p r ∧
    (∀ i, IsVtOver A L p (· = r i) s (r i ^ p) (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L.L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.L.ι) : Z.presheaf.stalk z :=
  sval (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J

variable {A L Ψ k}

theorem prod_iso {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) {U : Type} [CommGroup U] (h : (Z ⟶ A.left) → U) :
    ∏ i, h (r ≫ isoφ A Ψ i) ^ (![k, -1] : Fin 2 → ℤ) i =
      h (r ≫ (snd (Over.mk x) A).left) ^ k * (h (r ≫ Ψ ≫ (snd (Over.mk x') A).left))⁻¹ := by
  rw [Fin.prod_univ_two, ← zpow_neg_one]; rfl

theorem prod_iso' {U : Type} [CommGroup U] (h : ((Over.mk x ⊗ A).left ⟶ A.left) → U) :
    ∏ i, h (isoφ A Ψ i) ^ (![k, -1] : Fin 2 → ℤ) i =
      h (snd (Over.mk x) A).left ^ k * (h (Ψ ≫ (snd (Over.mk x') A).left))⁻¹ := by
  rw [Fin.prod_univ_two, ← zpow_neg_one]; rfl

variable {β : LB.Gen (isoLB A L Ψ k)} {s' : LB.Sec (LPow A L.L 1 (Over.mk x'))}
  {t t' : LB.Sec (LPow A L.L k (Over.mk x))} {U : ThetaGrp A L.L k (Over.mk x)}

theorem IsCarried.val (h : IsCarried A L Ψ k β s' t) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) : sv A L t r z J = sv A L s' (r ≫ Ψ) z J * (val β r z J).val :=
  (secRel_iff L.isLB _ _ t _ _ s' Ψ _ _ β).1 h Z r z J hJ

theorem isCarried_of_val (h : ∀ z J, Good L.L z J →
    sv A L t (𝟙 _) z J = sv A L s' (𝟙 _ ≫ Ψ) z J * (val β (𝟙 _) z J).val) : IsCarried A L Ψ k β s' t :=
  (secRel_iff L.isLB _ _ t _ _ s' Ψ _ _ β).2 h

omit [GrpObj A] in

theorem sec_ext {X : Scheme.{0}} {M : LB X} {a b : LB.Sec M} (h : ∀ j, a.f j = b.f j) : a = b := by
  cases a; cases b; congr; exact funext h

theorem IsCarried.unique (h : IsCarried A L Ψ k β s' t) (h' : IsCarried A L Ψ k β s' t') : t = t' :=
  sec_ext (sec_ext_val (L := L.L) (φ := fun _ : Fin 1 => (snd (Over.mk x) A).left) L.isLB fun z _ hJ =>
    (h.val _ z hJ).trans (h'.val _ z hJ).symm)

theorem exists_isCarried (hβ : β.IsGen) (s' : LB.Sec (LPow A L.L 1 (Over.mk x'))) :
    ∃ t, IsCarried A L Ψ k β s' t := by
  obtain ⟨t, ht⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd (Over.mk x) A).left) (ε' := fun _ => k)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := V) _ (Fin.prod_univ_one _) (prod_iso' h)).trans ?_
      rw [Fin.prod_univ_one]
      simp only [Sum.elim_inl, zpow_one]
      rw [mul_comm, inv_mul_cancel_right])
    (pullMulSec (L := L.L) (φ := fun _ : Fin 1 => (snd (Over.mk x') A).left) (ε := fun _ => 1) s' Ψ β hβ)
  exact ⟨t, isCarried_of_val fun z J hJ => (ht _ _ z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ)⟩

abbrev uv {T : Over S} (U : ThetaGrp A L.L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![k, -k]) U.φ r z J

theorem val_desc (c : Over.mk x ⟶ A) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (translT A c).left))) r z J =
      val β r z J * (val β (r ≫ (translT A c).left) z J)⁻¹ := by
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem IsDescLift.val (h : IsDescLift A L Ψ k β U) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) : uv U r z J = val β r z J * (val β (r ≫ (translT A U.pt).left) z J)⁻¹ :=
  (val_corr hJ h.2 r).trans (val_desc _ r z hJ)

theorem exists_isDescLift (hβ : β.IsGen) {c : Over.mk x ⟶ A} (hc : c ∈ transKer A Ψ) :
    ∃ U : ThetaGrp A L.L k (Over.mk x), U.pt = c ∧ IsDescLift A L Ψ k β U := by
  obtain ⟨u, hu, hv⟩ := exists_gen L.isLB (φ' := ![(snd (Over.mk x) A).left, (translPt A c).left]) (ε' := ![k, -k])
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_iso' h)
        (prod_neg _ _ (prod_iso (translT A c).left h))).trans ?_
      rw [Fin.prod_univ_two, ← Category.assoc, mem_transKer.1 hc, ← Over.comp_left, translT, lift_snd]
      simp only [Matrix.cons_val, zpow_neg, mul_inv, inv_inv]
      rw [mul_comm (h (translPt A c).left ^ k)⁻¹, ← _root_.mul_assoc, inv_mul_cancel_right])
    (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (translT A c).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
  exact ⟨⟨c, u, hu⟩, rfl, hc, corr_of_val L.isLB fun z J hJ => hv _ _ z J hJ⟩

theorem IsDescLift.unique {U' : ThetaGrp A L.L k (Over.mk x)} (h : IsDescLift A L Ψ k β U)
    (h' : IsDescLift A L Ψ k β U') (e : U.pt = U'.pt) : LB.Gen.Corr L.L _ _ _ _ U.φ U'.φ :=
  corr_of_val L.isLB fun z J hJ => (h.val _ z hJ).trans (by rw [e]; exact (h'.val _ z hJ).symm)

theorem act_val {T : Over S} {U : ThetaGrp A L.L k T} {a b : LB.Sec (LPow A L.L k T)} (h : IsActOf A L.L k U a b)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    sv A L b r z J = (uv U r z J).val * sv A L a (r ≫ (translT A U.pt).left) z J := twist_val h r z hJ

theorem exists_isActOf {T : Over S} (U : ThetaGrp A L.L k T) (a : LB.Sec (LPow A L.L k T)) :
    ∃ b, IsActOf A L.L k U a b := by
  obtain ⟨b, hb⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => k)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := V) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, zpow_neg]
      rw [← Over.comp_left, translT, lift_snd, mul_comm, inv_mul_cancel_right])
    (pullMulSec (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) a (translT A U.pt).left
      (φ₃ := ![(snd T A).left, (translPt A U.pt).left]) (ε₃ := ![k, -k]) U.φ U.isGen)
  exact ⟨b, twist_of_val L.isLB U.isGen fun z J hJ =>
    (hb _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans (mul_comm _ _))⟩

theorem sv_sum {T : Over S} {n : ℕ} {a : LB.Sec (LPow A L.L k T)} {F : Fin n → LB.Sec (LPow A L.L k T)}
    (h : ∀ j, a.f j = ∑ i, (F i).f j) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    sv A L a r z J = ∑ i, sv A L (F i) r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem sum_of_sv {T : Over S} {n : ℕ} {a : LB.Sec (LPow A L.L k T)} {F : Fin n → LB.Sec (LPow A L.L k T)}
    (h : ∀ z J, Good L.L z J → sv A L a (𝟙 _) z J = ∑ i, sv A L (F i) (𝟙 _) z J) (j) :
    a.f j = ∑ i, (F i).f j := by
  let b : LB.Sec (LPow A L.L k T) := SecM.toSec A (∑ i, SecM.ofSec A (F i))
  have hb : ∀ j, b.f j = ∑ i, (F i).f j := fun j => by
    show (∑ i, SecM.ofSec A (F i) : SecM A L.L k T).1 j = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  rw [← hb]
  exact sec_ext_val (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) L.isLB
    (fun z J hJ => (h z J hJ).trans (sv_sum hb _ z hJ).symm) j

theorem isThetaTrace_iff {p : ℕ} {s : LB.Sec (LPow A L.L 1 (Over.mk x))} :
    IsThetaTrace A L Ψ p s s' ↔
      ∃ (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x)))
        (n : ℕ) (c : Fin n → (Over.mk x ⟶ A)),
        IsRigIso A L Ψ _ β ∧ IsMulPull A L p s s₁ ∧ IsRepsModTors (transKer A Ψ) p c ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
          sv A L s' (r ≫ Ψ) z J = ∑ i, ((val β (r ≫ (translT A (c i)).left) z J)⁻¹).val *
            sv A L s₁ (r ≫ (translT A (c i)).left) z J := by
  constructor
  · rintro ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩
    refine ⟨β, s₁, n, fun i => (U i).pt, hβ, hs, hr, fun Z r z J hJ => ?_⟩
    rw [← Units.mul_left_inj (val β r z J), ← ht.val r z hJ, sv_sum hsum r z hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_val (hF i) r z hJ, (hU i).val r z hJ, Units.val_mul]
    ring
  · rintro ⟨β, s₁, n, c, hβ, hs, hr, hv⟩
    obtain ⟨t, ht⟩ := exists_isCarried hβ.2.1 s'
    choose U hc hU using fun i => exists_isDescLift hβ.2.1 (hr.1 i)
    choose F hF using fun i => exists_isActOf (U i) s₁
    obtain rfl : c = fun i => (U i).pt := funext fun i => (hc i).symm
    refine ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, sum_of_sv fun z J hJ => ?_⟩
    rw [ht.val _ z hJ, hv _ _ z J hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_val (hF i) _ z hJ, (hU i).val _ z hJ, Units.val_mul]
    ring

theorem sv_smul {T : Over S} {a : Γ(T.left, ⊤)} {u v : LB.Sec (LPow A L.L k T)}
    (h : ∀ j, v.f j = liftFun A _ a * u.f j) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) : sv A L v r z J = gs (r ≫ (fst T A).left) z ⊤ a * sv A L u r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  refine (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  exact (gs_res r z le_top hm _).trans (gs_pull r (fst T A).left z ⊤ trivial a)

theorem IsThetaTrace.smul {p : ℕ} {s u : LB.Sec (LPow A L.L 1 (Over.mk x))} {u' : LB.Sec (LPow A L.L 1 (Over.mk x'))}
    (h : IsThetaTrace A L Ψ p s s') (a : Γ(Y, ⊤))
    (hu : ∀ j, u.f j = liftFun A (T := Over.mk x) _ a * s.f j)
    (hu' : ∀ j, u'.f j = liftFun A (T := Over.mk x') _ a * s'.f j) : IsThetaTrace A L Ψ p u u' := by
  obtain ⟨β, s₁, n, c, hβ, ⟨α₀, α, g₀, n₀, cα, tw⟩, hr, hv⟩ := isThetaTrace_iff.1 h
  let u₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x)) :=
    SecM.toSec A ((show Γ((Over.mk x).left, ⊤) from a) • SecM.ofSec A s₁)
  have h₁ : ∀ j, u₁.f j = liftFun A (T := Over.mk x) _ a * s₁.f j := fun _ => rfl
  refine isThetaTrace_iff.2 ⟨β, u₁, n, c, hβ, ⟨α₀, α, g₀, n₀, cα, fun j => fn_ext fun z hz => ?_⟩, hr,
    fun Z r z J hJ => ?_⟩
  · have e := congrArg (gs (𝟙 _) z _) (tw j)
    have hz' : (𝟙 (Over.mk x ⊗ A).left : _ ⟶ _) z ∈
      LB.wchart L.L ![(snd (Over.mk x) A).left, (snd (Over.mk x) A ^ p).left] j := hz
    have l₀ := chart_le_zero A L.L (snd (Over.mk x) A ^ p) j
    have l₁ := chart_le_pull A L.L (mulT A (Over.mk x) p) (snd (Over.mk x) A ^ p) (lift_snd _ _) j
    have a₀ := fun w => gs_res (𝟙 _) z l₀ hz' w
    have a₁ := fun w => (gs_res (𝟙 _) z l₁ hz' (((mulT A (Over.mk x) p).left.app _).hom w)).trans
      (gs_pull (𝟙 _) (mulT A (Over.mk x) p).left z
        (LB.wchart L.L (fun _ : Fin 1 => (snd (Over.mk x) A).left) fun _ => j 1) (l₁ hz') w)
    have b₀ : gs (𝟙 _) z _ (u₁.f fun _ => j 0) = gs (𝟙 _ ≫ (fst (Over.mk x) A).left) z ⊤ a * _ :=
      (gs_mul (𝟙 _) z _ (l₀ hz') _ _).trans (congrArg₂ (· * ·)
        ((gs_res _ z le_top (l₀ hz') _).trans (gs_pull _ (fst (Over.mk x) A).left z ⊤ trivial a)) rfl)
    have m₁ : (𝟙 _ ≫ (mulT A (Over.mk x) p).left) z ∈
      LB.wchart L.L (fun _ : Fin 1 => (snd (Over.mk x) A).left) fun _ => j 1 := l₁ hz'
    have b₁ : gs (𝟙 _ ≫ (mulT A (Over.mk x) p).left) z _ (u.f fun _ => j 1) =
        gs ((𝟙 _ ≫ (mulT A (Over.mk x) p).left) ≫ (fst (Over.mk x) A).left) z ⊤ a * _ :=
      (congrArg (gs _ z _) (hu _)).trans ((gs_mul _ z _ m₁ _ _).trans (congrArg₂ (· * ·)
        ((gs_res _ z le_top m₁ _).trans (gs_pull _ (fst (Over.mk x) A).left z ⊤ trivial a)) rfl))
    rw [Category.assoc, ← Over.comp_left, mulT, lift_fst] at b₁
    have e' := (a₀ _).symm.trans (e.trans ((gs_mul _ z _ hz' _ _).trans (congrArg₂ (· * ·) rfl (a₁ _))))
    refine (a₀ _).trans (b₀.trans (Eq.trans ?_ ((gs_mul _ z _ hz' _ _).trans
      (congrArg₂ (· * ·) rfl ((a₁ _).trans b₁))).symm))
    exact (congrArg (_ * ·) e').trans (mul_left_comm _ _ _)
  · rw [sv_smul (T := Over.mk x') hu' _ z hJ, hv _ r z J hJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sv_smul (T := Over.mk x) h₁ _ z hJ, Category.assoc, Category.assoc, hβ.1.1, ← Over.comp_left, translT, lift_fst]
    exact mul_left_comm _ _ _

theorem val_rigT (T : Over S) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L.L z J) :
    val (rigT A L.L L.rig T k) r z J =
      val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (r ≫ T.hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  refine Eq.trans ?_ (val_of (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => congrArg J (Category.assoc _ _ _))).symm
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart L.L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem isPointed_mulT (p : ℕ) : IsPointed A (x := x) (x' := x) (mulT A (Over.mk x) p).left := by
  constructor
  · rw [← Over.comp_left, mulT, lift_fst]
  · rw [← Over.comp_left, mulT, ptSecT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd, one_pow]

theorem mem_transKer_mulT [IsCommMonObj A] {T : Over S} (p : ℕ) (c : T ⟶ A) :
    c ∈ transKer A (mulT A T p).left ↔ c ^ p = 1 := by
  have e : translT A c ≫ mulT A T p = lift (fst T A) ((fst T A ≫ c ^ p) * snd T A ^ p) := by
    rw [mulT, translT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd, translPt_eq, mul_pow, MonObj.comp_pow]
  rw [mem_transKer, ← Over.comp_left, e]
  constructor
  · intro h
    have h' := congrArg (fun q => lift (𝟙 T) (1 : T ⟶ A) ≫ q ≫ snd T A) (Over.OverMorphism.ext h)
    simpa [mulT, MonObj.comp_mul, MonObj.comp_pow] using h'
  · intro h
    rw [h, MonObj.comp_one, _root_.one_mul, mulT]

theorem IsMulPull.exists_isRigIso {p : ℕ} {s : LB.Sec (LPow A L.L 1 (Over.mk x))}
    {s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))} (h : IsMulPull A L p s s₁) :
    ∃ β, IsRigIso A L (mulT A (Over.mk x) p).left _ β ∧ IsCarried A L (mulT A (Over.mk x) p).left _ β s s₁ := by
  obtain ⟨α₀, α, g₀, n₀, cα, tw⟩ := h
  obtain ⟨β, hβ, hv⟩ := exists_gen L.isLB (φ' := isoφ A (mulT A (Over.mk x) p).left) (ε' := ![(p : ℤ) ^ 2, -1])
    (fun V _ h => by
      rw [prod_mulN p (snd (Over.mk x) A) h, prod_iso', ← Over.comp_left, mulT, lift_snd, ← Nat.cast_pow, zpow_natCast])
    (LB.pullGen L.L _ _ α₀ (snd (Over.mk x) A).left) (pullGen_isGen _ _ _ _ g₀ _)
  refine ⟨β, ⟨isPointed_mulT p, hβ, corr_of_val L.isLB fun z J hJ => ?_⟩, isCarried_of_val fun z J hJ => ?_⟩
  · have e := val_corr hJ n₀ (𝟙 _ ≫ x)
    rw [val_pull hJ, val_mul hJ, val_inv] at e
    have e₁ : ((𝟙 Y ≫ (ptSecT A (1 : Over.mk x ⟶ A)).left) ≫ (snd (Over.mk x) A).left) = (𝟙 _ ≫ x) ≫ eSec A := by
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]; rfl
    refine (val_pull hJ _ _ _).trans ((hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_))
    refine (congrArg (fun q => val α₀ q z J) e₁).trans (e.trans (Eq.trans ?_ (val_mul hJ _ _ _).symm))
    exact congrArg₂ (· * ·) ((map_zpow _ _ _).trans (val_rigT (Over.mk x) _ (𝟙 Y) z hJ).symm)
      ((zpow_neg_one _).symm.trans (val_rigT (Over.mk x) _ (𝟙 Y) z hJ).symm)
  · rw [hv _ _ z J hJ, ← val_corr hJ cα]
    exact (twist_val tw _ z hJ).trans (mul_comm _ _)

theorem isThetaTrace_mulT [IsCommMonObj A] {p : ℕ} {s : LB.Sec (LPow A L.L 1 (Over.mk x))}
    {s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))} (h : IsMulPull A L p s s₁) :
    IsThetaTrace A L (mulT A (Over.mk x) p).left p s s := by
  obtain ⟨β, hβ, hc⟩ := h.exists_isRigIso
  refine isThetaTrace_iff.2 ⟨β, s₁, 1, fun _ => 1, hβ, h, ⟨fun _ => Subgroup.one_mem _, fun c hc =>
    ⟨0, by simpa using (mem_transKer_mulT p c).1 hc, fun _ _ => Subsingleton.elim _ _⟩⟩, fun Z r z J hJ => ?_⟩
  rw [Fin.sum_univ_one, hc.val _ z hJ, translT_one, Over.id_left, Category.comp_id, mul_comm,
    Units.mul_inv_cancel_right]

theorem IsRepsModTors.card {G : Type} [CommGroup G] {C : Subgroup G} {p n : ℕ} {r : Fin n → G}
    (h : IsRepsModTors C p r) : Nat.card C = Nat.card {c : G // c ∈ C ∧ c ^ p = 1} * n := by
  have : Function.Bijective fun q : {c : G // c ∈ C ∧ c ^ p = 1} × Fin n =>
      (⟨q.1.1 * r q.2, C.mul_mem q.1.2.1 (h.1 _)⟩ : C) := by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ e
      have e' : a.1 * r i = b.1 * r j := congrArg Subtype.val e
      obtain rfl : i = j := (h.2 _ (C.mul_mem a.2.1 (h.1 i))).unique (by simpa using a.2.2)
        (by rw [e']; simpa using b.2.2)
      exact Prod.ext (Subtype.ext (mul_right_cancel e')) rfl
    · intro c
      obtain ⟨i, hi, -⟩ := h.2 c c.2
      exact ⟨(⟨c * (r i)⁻¹, C.mul_mem c.2 (C.inv_mem (h.1 i)), hi⟩, i), Subtype.ext (by simp)⟩
  rw [← Nat.card_eq_of_bijective _ this, Nat.card_prod, Nat.card_fin]

theorem exists_isRepsModTors {G : Type} [CommGroup G] (C : Subgroup G) [Finite C] (p : ℕ) :
    ∃ (n : ℕ) (r : Fin n → G), IsRepsModTors C p r := by
  let D : Subgroup C := (powMonoidHom p : C →* C).ker
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (C ⧸ D)
  have key : ∀ a b : C, ((a : G) * (b : G)⁻¹) ^ p = 1 ↔ (b : C ⧸ D) = a := fun a b => by
    rw [QuotientGroup.eq, MonoidHom.mem_ker, powMonoidHom_apply, Subtype.ext_iff, mul_comm]
    simp
  refine ⟨n, fun i => (e.symm i).out, fun i => Subtype.property _, fun c hc =>
    ⟨e ((⟨c, hc⟩ : C) : C ⧸ D), (key ⟨c, hc⟩ _).2 (by simp), fun j hj => ?_⟩⟩
  have := (key ⟨c, hc⟩ _).1 hj
  rw [QuotientGroup.out_eq'] at this
  rw [← this, Equiv.apply_symm_apply]

theorem IsRigIso.val_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {β' : LB.Gen (isoLB A L Ψ k)}
    (h : IsRigIso A L Ψ k β) (h' : IsRigIso A L Ψ k β') {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) : val β r z J = val β' r z J :=
  gen_unique L.isLB (fst (Over.mk x) A).left (ptSecT A (1 : Over.mk x ⟶ A)).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG hA _) h.2.1 h'.2.1 (fun w I hI => by
      have a := val_corr hI h.2.2 (𝟙 _)
      have b := val_corr hI h'.2.2 (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm) _ r z J hJ

theorem IsMulPull.unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {p : ℕ} {s : LB.Sec (LPow A L.L 1 (Over.mk x))}
    {s₁ s₂ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))} (h₁ : IsMulPull A L p s s₁) (h₂ : IsMulPull A L p s s₂) :
    s₁ = s₂ := by
  obtain ⟨β₁, a₁, b₁⟩ := h₁.exists_isRigIso
  obtain ⟨β₂, a₂, b₂⟩ := h₂.exists_isRigIso
  exact sec_ext (sec_ext_val (L := L.L) (φ := fun _ : Fin 1 => (snd (Over.mk x) A).left) L.isLB fun z _ hJ =>
    (b₁.val _ z hJ).trans ((congrArg (fun q => _ * Units.val q) (a₁.val_unique hG hA a₂ _ z hJ)).trans
      (b₂.val _ z hJ).symm))

theorem IsDescLift.symLift [IsCommMonObj A] (h : IsDescLift A L Ψ k β U) (hβ : β.IsGen) (hs : L.IsSymmetric)
    (hneg : (negT A (Over.mk x)).left ≫ Ψ = Ψ ≫ (negT A (Over.mk x')).left) {n : ℕ} (hn : U.pt ^ n = 1) :
    SymLift A L.L k n U.pt U := by
  refine ⟨rfl, corr_of_val L.isLB fun z J hJ => ?_, ?_⟩
  · let f : ℕ → _ := fun j => Geo.Tor.val β (𝟙 _ ≫ (translT A (U.pt ^ j)).left) z J
    have e : ∀ j : Fin n, Geo.Tor.val U.φ (𝟙 _ ≫ (translT A (U.pt ^ (j : ℕ))).left) z J = f j / f (j + 1) := fun j => by
      refine (h.val _ z hJ).trans ?_
      rw [Category.assoc, ← Over.comp_left, ← translT_mul, ← pow_succ', div_eq_mul_inv]
    rw [val_powGenT U n _ z hJ, val_one, Finset.prod_congr rfl fun j _ => e j,
      Fin.prod_univ_eq_prod_range (fun j => f j / f (j + 1)), Finset.prod_range_div']
    simp only [f, hn, pow_zero, div_self']
  · obtain ⟨-, ws, gws, -⟩ := hs
    obtain ⟨ν₀, hν₀⟩ := gen_of_iso ((isGen_iff ws).1 gws) (snd (Over.mk x') A).left
    obtain ⟨ν, hν, hv⟩ := exists_gen L.isLB
      (φ' := ![(snd (Over.mk x) A).left, (snd (Over.mk x) A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε' := ![k, -k])
      (fun V _ g => by
        refine (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _ (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
          (prod_iso' g) (prod_neg _ _ (prod_iso (negT A (Over.mk x)).left g)))
          (prod_neg _ _ (Fin.prod_univ_two _))).trans ?_
        rw [Fin.prod_univ_two, ← Category.assoc, hneg, Category.assoc, ← Over.comp_left, ← Over.comp_left, negT, negT,
          lift_snd, lift_snd]
        simp only [Sum.elim_inr, Matrix.cons_val, Over.comp_left]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        module)
      (LB.mulGen L.L _ _ _ _
        (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (negT A (Over.mk x)).left)))
        (LB.invGen L.L _ _ (LB.pullGen L.L _ _ ν₀ Ψ)))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hν₀ _)))
    refine ⟨ν, hν, corr_of_val L.isLB fun z J hJ => ?_⟩
    have hv' : ∀ r, Geo.Tor.val ν r z J = Geo.Tor.val β r z J * (Geo.Tor.val β (r ≫ (negT A (Over.mk x)).left) z J)⁻¹ *
        (Geo.Tor.val ν₀ (r ≫ Ψ) z J)⁻¹ := fun r => by
      rw [hv _ r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ]
    have e₁ : (translT A U.pt⁻¹).left ≫ (translT A U.pt).left = 𝟙 _ := by
      rw [← Over.comp_left, ← translT_mul, mul_inv_cancel, translT_one]; rfl
    have e₂ : (translT A U.pt⁻¹).left ≫ (negT A (Over.mk x)).left =
        (negT A (Over.mk x)).left ≫ (translT A U.pt).left := by
      have i : ∀ {T : Over S} (a : T ⟶ A), a ≫ (GrpObj.inv : A ⟶ A) = a⁻¹ := fun _ => rfl
      rw [← Over.comp_left, ← Over.comp_left, negT, lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc,
        translPt_eq, i, i, mul_inv, GrpObj.comp_inv, inv_inv]
    refine (val_symGen U ν _ z hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (h.val _ z hJ) (hv' _))
      (congrArg₂ (· * ·) (h.val _ z hJ) (congrArg (·⁻¹) (hv' _)))).trans ?_
    simp only [Category.id_comp, e₁, e₂, mem_transKer.1 ((transKer A Ψ).inv_mem h.1)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

theorem IsThetaTrace.sv_eq_of_mulT [IsCommMonObj A] (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {p : ℕ}
    {s u : LB.Sec (LPow A L.L 1 (Over.mk x))} (h : IsThetaTrace A L (mulT A (Over.mk x) p).left p s u)
    {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    sv A L u (r ≫ (mulT A (Over.mk x) p).left) z J = sv A L s (r ≫ (mulT A (Over.mk x) p).left) z J := by
  obtain ⟨β, s₁, n, c, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 h
  obtain ⟨β', hβ', hc⟩ := hs.exists_isRigIso
  obtain ⟨i, -, hi⟩ := hr.2 1 (Subgroup.one_mem _)
  have hu : ∀ j, j = i := fun j => hi j (by simpa using (mem_transKer_mulT p _).1 (hr.1 j))
  rw [hv _ r z J hJ, Finset.sum_eq_single i (fun j _ hj => absurd (hu j) hj) (fun h => absurd (Finset.mem_univ i) h),
    hc.val _ z hJ, hβ.val_unique hG hA hβ' _ z hJ, Category.assoc, mem_transKer.1 (hr.1 i), mul_comm,
    Units.mul_inv_cancel_right]

end General

section Hecke

open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def thetaTransport (p : ℕ) : Transport Xo c :=
  fun _ _ _ _ _ _ Ψ s s' => IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s'

def hkTr (p : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω)
    (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) : Prop :=
  IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x ψ) p y.s z.s

def hkTrSym (p : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω)
    (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) : Prop :=
  IsThetaTraceSym Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x ψ) p y.s z.s

variable {Xo c}

section Isog

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} {x x' : Sp Ω ⟶ Xo.X}
  {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x'}
  {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}

theorem gx_hom_ext {f g : Gx x ⟶ Gx x'}
    (hf : f ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hg : g ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (h : ∀ a : Over.mk x ⟶ Xo.univ.t.G, (lift (𝟙 (Over.mk x)) a).left ≫ f = (lift (𝟙 (Over.mk x)) a).left ≫ g) :
    f = g := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
    show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp Ω))
  have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
  refine ext_of_points (fst (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
    (hf.trans hg.symm) fun q hq => ?_
  let a : Over.mk x ⟶ Xo.univ.t.G := Over.homMk (q ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hq]; rfl)
  have e : q = (lift (𝟙 (Over.mk x)) a).left := by
    refine gx_ext ?_ ?_
    · rw [hq, lift_l_fst]; rfl
    · rw [lift_l_snd]; rfl
  rw [e]
  exact h a

theorem isPointed_of_isHkIsog (h : IsHkIsog p x x' C ψ ψp) : IsPointed Xo.univ.t.G (conj x x' ψ) :=
  ⟨(over_iff ψ).2 h.2.1, by
    have := (sends_conj_iff ψ _ _).2 (h.2.2.1 1)
    rwa [map_one] at this⟩

theorem transKer_of_isHkIsog (h : IsHkIsog p x x' C ψ ψp) : transKer Xo.univ.t.G (conj x x' ψ) = C := by
  obtain ⟨-, h0, hf, -, -, rfl, -⟩ := h
  have h0' := (over_iff ψ).2 h0
  have hf' : ∀ a, (lift (𝟙 (Over.mk x)) a).left ≫ conj x x' ψ = (lift (𝟙 (Over.mk x')) (ψp a)).left :=
    fun a => (sends_conj_iff ψ _ _).2 (hf a)
  have ht : ∀ a b : Over.mk x ⟶ Xo.univ.t.G, (lift (𝟙 (Over.mk x)) a).left ≫ (translT _ b).left =
      (lift (𝟙 (Over.mk x)) (b * a)).left := fun a b => by
    rw [← Over.comp_left, lift_transl, Category.id_comp]
  ext b
  rw [mem_transKer, MonoidHom.mem_ker]
  constructor
  · intro e
    have e' := congrArg ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ ·) e
    simp only [← Category.assoc, ht, _root_.mul_one] at e'
    rw [← map_one ψp]
    exact sends_unique (hf' b) (e'.trans (hf' 1))
  · intro hb
    refine gx_hom_ext (by rw [Category.assoc, h0', ← Over.comp_left, translT, lift_fst]) h0' fun a => ?_
    rw [← Category.assoc, ht, hf', hf', map_mul, hb, _root_.one_mul]

theorem card_reps {P : Ideal (𝓞 E)} {i n : ℕ} (hp : 0 < p) (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C)
    {r : Fin n → (Over.mk x ⟶ Xo.univ.t.G)} (hr : IsRepsModTors C p r) : n = Ideal.absNorm P ^ i := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ Xo.s)
  have h₀ := (HeckeKerModel.heckeKer_zero Xo.univ Ω x β.hom hβ.symm P p hp).2.2.2.2.1
  have h₁ := hC.2.2.2.2.1
  have h₂ := hC.2.2.2.2.2
  have h₃ := hr.card
  have e : Nat.card {c // c ∈ C ∧ c ^ p = 1} = Nat.card ((C : Set (Over.mk x ⟶ Xo.univ.t.G)) ∩
      Xo.univ.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk x ⟶ Xo.univ.t.G)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a =>
      and_congr_right fun _ => (HeckeKerModel.mem_tors_span _ a p).symm)
  have h₄ := h₃.symm.trans (h₁.trans (h₀.symm.trans (h₂.trans (by rw [← e]))))
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero fun h0 => ?_) h₄
  rw [h0, zero_mul, h₁] at h₃
  exact pow_ne_zero _ hp.ne' h₃

end Isog

theorem exists_isMulPull (p : ℕ) {T : Over Xo.X} (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) :
    ∃ s₁, IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ := by
  obtain ⟨α₀, g₀, n₀, -, hT⟩ := moduli_univ_normMul abelianSchemeLaws_all.1 E H Dw l Xo p
  obtain ⟨α, gα, cα⟩ := hT T
  obtain ⟨b, hb⟩ := exists_sec Xo.univ.t.PP.isLB (φ' := fun _ : Fin 1 => (snd T Xo.univ.t.G).left)
    (ε' := fun _ => (p : ℤ) ^ 2) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := V) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, zpow_neg, zpow_one]
      rw [← Over.comp_left, mulT, lift_snd, mul_comm, inv_mul_cancel_right])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T Xo.univ.t.G).left) (ε := fun _ => 1) s (mulT Xo.univ.t.G T p).left α gα)
  exact ⟨b, α₀, α, g₀, n₀, cα, twist_of_val Xo.univ.t.PP.isLB gα fun z J hJ =>
    (hb _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans (mul_comm _ _))⟩

example : IsRepsModTors (⊤ : Subgroup ℤˣ) 3 ![1, -1] := by
  refine ⟨fun _ => trivial, fun c _ => ?_⟩
  rcases Int.units_eq_one_or c with rfl | rfl
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

example (P : Ideal (𝓞 E)) (p i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω)
    (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω) : Prop := hkRelFr P p i (hkTr Xo c p) Ω y C z

end Hecke

end GlobalTheory.ThetaTrace
