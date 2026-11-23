import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Defs
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

def ThG (m : ℕ) {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (x : T ⟶ G) (c : Γ(T.left, ⊤)) : Prop :=
  x ^ (m ^ 2) = 1 ∧ ∃ (t : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T))
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, (snd T G ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T)) (θ : ThetaGrp G L ((m ^ 2 : ℕ) : ℤ) T),
    α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT G 1).left) (rigT G L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull G L (mulT G _ m) (snd _ G ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift G L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf G L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good L z J → VVRank.sv G t (ptSecT G 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (rigT G L ρ T ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val

def NZ {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) : Prop :=
  ∃ g : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left g = closedPoint V ∧ g ∈ nonzeroLocus σ

def UnivBasis {K : Type} [CommRing K] (x : Sp K ⟶ S) (e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [CommRing K'] (i : K →+* K') (x' : Sp K' ⟶ S) (h : spMap i ≫ x = x') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')),
    ∃! c : Γ((Over.mk x').left, ⊤),
      s = c • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)

variable {G L} in

def IsRigidificationPullbackCompatibleIso {S' : Scheme.{0}} {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left} {L' : LB A.left} (w : LB.Iso L' (L.pull φ))
    (f : S' ⟶ S) (ρ' : LB.Gen (L'.pull (eSec A))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (J) (J'), Good L z J → Good L' z J' →
    val (L := L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ (r ≫ f) z J =
      wVal w z J J' (r ≫ eSec A) * val (L := L') (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ' r z J'
end Defs

theorem thG_iff {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : GlobalTheory.UT.SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (c : F) :
    ThG A.A A.L ρ m th x (fnOf c) ↔ x ^ (m ^ 2) = 1 ∧ ∃ t, GlobalTheory.UT.ThC A ρ m th x t c := Iff.rfl

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}

theorem val_rigT (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T₀.left) (z : Z) {J} (hJ : Good L₀ z J) :
    val (rigT G L₀ ρ₀ T₀ k) r z J =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T₀.hom ≫ eSec G) r
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J
    (fun _ => J (r ≫ T₀.hom ≫ eSec G)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hz _).trans (gm_pull r T₀.hom z _ (rigT_le G L₀ _ hz) _)

include hτ in

theorem IsRigidificationPullbackCompatibleIso.rigT (h : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'}
    (hJ : Good L₀ z J) (hJ' : Good L₁ z J') : val (rigT G L₀ ρ₀ T₀ k) (r ≫ τ) z J =
      wVal w z J J' (r ≫ T.hom ≫ eSec A) ^ k * val (rigT A L₁ ρ₁ T k) r z J' := by
  rw [val_rigT k _ z hJ, val_rigT k _ z hJ', Category.assoc, hτ, ← Category.assoc, h _ _ z J J' hJ hJ', mul_zpow,
    Category.assoc]

theorem norm_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ} {a : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
      val α₀ (r ≫ psi hp τ hτ) z J = (wVal w z J J' (r ≫ (snd T A).left) ^ a *
        wVal w z J J' (r ≫ (snd T A ^ m).left) ^ (-((1 : ℕ) : ℤ))) * val α r z J')
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J') :
    val α₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = val (Out.rigT G L₀ ρ₀ T₀ (a - 1)) (r ≫ τ) z J ↔
      val α (r ≫ (ptSecT A 1).left) z J' = val (Out.rigT A L₁ ρ₁ T (a - 1)) r z J' := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    H _ _ _ _ _ hJ hJ', Category.assoc, Category.assoc, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, ← zpow_add,
    show a + -((1 : ℕ) : ℤ) = a - 1 from rfl, mul_right_inj]

theorem value_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {a : ℤ} {t₀ : LB.Sec (LPow G L₀ a T₀)} {t : LB.Sec (LPow A L₁ a T)}
    (ht : SecRel hp τ hτ w t t₀) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J')
    (c : Z.presheaf.stalk z) :
    VVRank.sv G t₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = c * (val (Out.rigT G L₀ ρ₀ T₀ a) (r ≫ τ) z J).val ↔
      VVRank.sv A t (r ≫ (ptSecT A 1).left) z J' = c * (val (Out.rigT A L₁ ρ₁ T a) r z J').val := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    ht _ _ _ _ _ hJ hJ', Category.assoc, NormTheta.ptSec_snd, Units.val_mul, mul_left_comm, Units.mul_right_inj]

theorem value_at {a : ℤ} {t : LB.Sec (LPow A L₁ a T)} {c : Γ(T.left, ⊤)} (hL₁ : L₁.IsLB)
    (h : ∀ z J, Good L₁ z J → VVRank.sv A t (ptSecT A 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) (𝟙 _) z J).val)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L₁ z J) :
    VVRank.sv A t (r ≫ (ptSecT A 1).left) z J = gs r z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) r z J).val :=
  sv_of_isValueAt (x := (1 : T ⟶ A)) (ρ := Out.rigT A L₁ ρ₁ T a) (isValueAt_of_sv hL₁ fun y J hJ => by
    rw [Category.id_comp]; exact h y J hJ) r z hJ

theorem ThG.move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T₀.left, ⊤)} (H : ThG G L₀ ρ₀ m th₀ x₀ c) : ThG A L₁ ρ₁ m th x (τ.appTop.hom c) := by
  obtain ⟨-, t₀, α₀, s₀, θ₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨t, ht⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ t₀
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α₀ h₁
  obtain ⟨θ, hθ, hθ'⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn h₄
  refine ⟨hn, t, α, s, θ, hα, corr_of_val hL₁ fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅, fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    rw [val_pull hJ']
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').1 ((val_pull hJ _ _ _).symm.trans (val_corr hJ h₂ _))
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := (value_iff hp τ hτ hr ht (𝟙 _) y hJ hJ' _).1 (value_at hL₀ h₆ (𝟙 _ ≫ τ) y hJ)
    rw [Category.id_comp (ptSecT A 1).left] at q
    exact q.trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem ThG.up [IsIso τ] [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x₀ ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T.left, ⊤)} (H : ThG A L₁ ρ₁ m th x c) : ThG G L₀ ρ₀ m th₀ x₀ ((inv τ).appTop.hom c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s
  obtain ⟨t₀, ht⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ t
  obtain ⟨α₀, hα, vα⟩ := ThetaPtUp.exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α h₁
  obtain ⟨θ₀, hθ, hθ'⟩ := ThetaPtUp.symLift_up hp τ hτ hw hL₀ hL₁ hx h₀ h₄
  refine ⟨hn, t₀, α₀, s₀, θ₀, hα, corr_of_val hL₀ fun y J hJ => ?_,
    ThetaPtUp.isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅,
    fun y J hJ => ?_⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    rw [val_pull hJ, ← IsIso.inv_hom_id τ]
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').2 ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' h₂ _))
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := (value_iff hp τ hτ hr ht (inv τ) y hJ hJ' _).2 (value_at hL₁ h₆ (inv τ) y hJ')
    rw [IsIso.inv_hom_id, Category.id_comp] at q
    exact q.trans (congrArg (· * _) ((gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])).symm)

theorem ThG.smul (hL₁ : L₁.IsLB) {m : ℕ} {x : T ⟶ A} {th th' : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {a c : Γ(T.left, ⊤)}
    (h : SecM.ofSec A th' = a • SecM.ofSec A th) (H : ThG A L₁ ρ₁ m th x c) : ThG A L₁ ρ₁ m th' x (a * c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  have tw : ∀ {p q : ℤ} {κ : T ⊗ A ⟶ A} {β} (_ : β.IsGen) {u u' : LB.Sec (LPow A L₁ q T)} {v : LB.Sec (LPow A L₁ p T)},
      SecM.ofSec A u' = a • SecM.ofSec A u → IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u v →
      IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u' (SecM.toSec A (a • SecM.ofSec A v)) := by
    intro p q κ β hβ u u' v hu hv
    refine VVRank.isTwistPull_of_sv A hL₁ hβ fun y J hJ => ?_
    have e₁ := sv_of_eq_mul (s := u') (t := u) (c := a) (fun j => congrArg (fun q => q.1 j) hu)
      (𝟙 _ ≫ (lift (fst T A) κ).left) y hJ
    have e₂ := sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A v)) (t := v) (c := a) (fun j => rfl) (𝟙 _) y hJ
    rw [e₁, e₂, VVRank.sv_of_isTwistPull A hv (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, lift_fst, mul_left_comm]
  refine ⟨h₀, SecM.toSec A (a • SecM.ofSec A t), α, SecM.toSec A (a • SecM.ofSec A s), θ, h₁, h₂, tw h₁ h h₃, h₄,
    tw θ.isGen rfl h₅, fun y J hJ => ?_⟩
  rw [sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A t)) (t := t) (c := a) (fun j => rfl) _ y hJ, h₆ y J hJ,
    ptSecT_fst, ← _root_.mul_assoc, gs_mul _ y ⊤ trivial]

include hp in

theorem exists_rigidificationPullbackCompatibleIso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hρ : ρ₀.IsGen) :
    ∃ ρ₁ : LB.Gen (L₁.pull (eSec A)), ρ₁.IsGen ∧ IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀ := by
  have e : eSec A ≫ φ = f ≫ eSec G := by
    have := over_one hp (T := baseOver S') (T₀ := baseOver S) f ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (f ≫ ·) (Category.id_comp _)))
  obtain ⟨ρ₁, h₁, h₂⟩ := exists_gen_through (φ' := fun _ : PUnit => eSec A) (φ := fun _ : PUnit => eSec G)
    (ε := fun _ => 1) (h := f) hw hL₀ hL₁ (fun _ => e) ρ₀ hρ
  exact ⟨ρ₁, h₁, fun Z r z J J' hJ hJ' => (h₂ Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])⟩

end Move

theorem ThG.unique (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} {m : ℕ} (hm : Odd m) (hu : IsUnit ((m ^ 2 : ℕ) : Γ(S, ⊤))) {T : Over S}
    {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {x : T ⟶ P.A} {c c' : Γ(T.left, ⊤)} (H : ThG P.A P.L ρ m th x c)
    (H' : ThG P.A P.L ρ m th x c') : c = c' := by
  obtain ⟨hx, t, α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ := H
  obtain ⟨-, t', α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩ := H'
  have hL := P.isLB
  obtain ⟨-, huniq⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns P.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  obtain rfl : s₁ = s₁' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A hs₁ _ y hJ).trans
      (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull P.A hs₁' _ y hJ).symm))
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  obtain rfl : t = t' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A ht _ y hJ).trans
      (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull P.A ht' _ y hJ).symm))
  refine fn_ext (V := ⊤) fun y _ => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory.Ex.OneGen
end
