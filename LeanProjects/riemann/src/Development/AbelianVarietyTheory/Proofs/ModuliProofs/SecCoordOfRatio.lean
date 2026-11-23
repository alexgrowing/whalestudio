import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompatOfLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out

theorem secCoord_of_ratio {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM' : M'.IsLB) {σ : Type} {th : σ → M.Sec}
    {th' : σ → M'.Sec} {B : Type} [Field B] {x : Sp B ⟶ X} {x' : Sp B ⟶ X'} (p : Sp B) {j : M.ι} {j' : M'.ι}
    (hj : x p ∈ M.U j) (hj' : x' p ∈ M'.U j') (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, gs x' p _ ((th' i).f j') = c * gs x p _ ((th i).f j)) {v : σ → B} (H : SecCoord M th x v) :
    SecCoord M' th' x' v := by
  have hs : ∀ y : Sp B, y = p := fun y => Subsingleton.elim (α := PrimeSpectrum B) _ _
  obtain ⟨u, hu⟩ := loc_of_secCoord H p j hj
  by_cases hv : Ideal.span (Set.range v) = ⊤
  · refine secCoord_of_loc hv fun y l hl => ?_
    obtain rfl := hs y
    refine ⟨gm x' y _ (M'.g l j') * (c * u), fun i => ?_⟩
    rw [gs_sec (th' i) x' y hl hj', h, hu, Units.val_mul, Units.val_mul]
    ring
  · have h0 : ∀ i, v i = 0 := fun i => by
      by_contra hi
      exact hv (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (IsUnit.mk0 _ hi))
    obtain ⟨w, hw⟩ := exists_secCoord (th := th') hM' (x := x') (k := j') fun y => by rw [hs y]; exact hj'
    obtain ⟨u', hu'⟩ := loc_of_secCoord hw p j' hj'
    have : w = v := funext fun i => ev_ext fun y => by
      obtain rfl := hs y
      have := hu' i
      rw [h, hu, h0, map_zero, zero_mul, mul_zero] at this
      rw [h0, map_zero]
      exact (Units.mul_left_eq_zero _).1 this.symm
    exact this ▸ hw

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem secCoord_of_sv {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {L : LB A.left} {L' : LB A'.left}
    (hL' : L'.IsLB) {a a' : ℤ} {T : Over S} {T' : Over S'} {σ : Type} {th : σ → LB.Sec (LPow A L a T)}
    {th' : σ → LB.Sec (LPow A' L' a' T')} {B : Type} [Field B] {x : Sp B ⟶ (T ⊗ A).left}
    {x' : Sp B ⟶ (T' ⊗ A').left} (p : Sp B) {I I'} (hI : Good L p I) (hI' : Good L' p I')
    (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, VVRank.sv A' (th' i) x' p I' = c * VVRank.sv A (th i) x p I) {v : σ → B}
    (H : SecCoord _ th x v) : SecCoord _ th' x' v :=
  secCoord_of_ratio (LB.isLB_linComb hL' _ _) p (hI.mem (fun _ : Fin 1 => (snd T A).left) x)
    (hI'.mem (fun _ : Fin 1 => (snd T' A').left) x') c h H

theorem lab_pow (t : TObj g (N' ^ 2) J b s) (a : Ix g (N' ^ 2)) : t.lab a ^ (N' ^ 2) = 1 := by
  have := t.ab.comm
  have cm : ∀ x y : Out.baseOver S ⟶ t.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ (N' ^ 2) = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, t.torsion, one_pow]

theorem MapBy.lab {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) (a : Ix g (N' ^ 2)) : f ≫ (t.lab a).left = (u.lab a).left ≫ φ := by
  have hτ : f ≫ (baseOver S).hom = (baseOver S').hom ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  refine (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).2 ?_
  simp only [TObj.lab, linComb, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_pow]
  congr 1
  exact (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).1 (h.2.2.1 i).symm

theorem emb_move {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) {m : ℕ} (hm : m ∣ N') {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ]
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {σ₀} (H : t.Emb m T₀ σ₀) : ∃ σ, u.Emb m T σ ∧
      ∀ (B : Type) [Field B] (y : Sp B ⟶ (T ⊗ u.A).left) (y₀ : Sp B ⟶ (T₀ ⊗ t.A).left),
        y₀ ≫ (fst T₀ t.A).left = y ≫ (fst T u.A).left ≫ τ → y₀ ≫ (snd T₀ t.A).left = y ≫ (snd T u.A).left ≫ φ →
        ∀ w, SecCoord _ σ y w ↔ SecCoord _ σ₀ y₀ w := by
  obtain ⟨w, hw⟩ := h.2.1
  have hp := h.1
  have hL₀ := t.isLB
  have hL₁ := u.isLB
  have := u.ab.comm
  obtain ⟨th₀, s₀, α₀, U₀, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th, hth⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s₁, hs⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose σ hσ using fun i => ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ (σ₀ i)
  obtain ⟨α, hα, vα⟩ := ThetaPtMove.exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) α₀ h₂
  have hx : ∀ a, τ ≫ ((Over.homMk T₀.hom (by simp) : T₀ ⟶ Out.baseOver S) ≫ t.lab a).left =
      ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a).left ≫ φ := fun a => by
    show τ ≫ T₀.hom ≫ _ = (T.hom ≫ _) ≫ φ
    rw [← Category.assoc, hτ, Category.assoc, h.lab, Category.assoc]
  have hk : ∀ a, (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 :=
    fun a => by
      rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  choose U hU hU' using fun i =>
    ThetaPtMove.symLift_move hp τ hτ hw hL₀ hL₁ (ThetaPtMove.over_pow hp τ hτ (hx i) _) (hk i) (h₅ i)
  have hg : IsGenSec t.A t.L 1 (VVRank.pullS t.A 1 (𝟙 T₀) th₀) :=
    ThetaCoord.isGenSec_pullS hL₀ _ (𝟙 T₀) (Category.comp_id _) h₁
  refine ⟨σ, ⟨th, s₁, α, U, ThetaPtMove.isGenSec_move hp τ hτ hw hL₀ hL₁ τ (𝟙 T₀) (Category.comp_id _) hth hg, hα,
    ThetaPtMove.isTwistPull_move hp τ hτ hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (hσ i) (h₆ i)⟩, fun B _ y y₀ e₁ e₂ v => ?_⟩
  obtain rfl : y₀ = y ≫ ThetaPtMove.psi hp τ hτ := ThetaPtMove.psi_ext
    (by rw [e₁, Category.assoc, ThetaPtMove.psi_fst']) (by rw [e₂, Category.assoc, ThetaPtMove.psi_snd'])
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL₀ p
  obtain ⟨I', hI'⟩ := ConstFam.exists_good' hL₁ p
  exact ⟨secCoord_of_sv hL₀ p hI' hI _ fun i => hσ i _ y p I I' hI hI',
    secCoord_of_sv hL₁ p hI hI' _ fun i => (Units.eq_inv_mul_iff_mul_eq _).2 (hσ i _ y p I I' hI hI').symm⟩

theorem emb_unique (hG : GlobalFnsSt) (t : TObj g (N' ^ 2) J b s) {m : ℕ} (hm : Odd m) {T : Over S}
    [Subsingleton T.left] {σ σ'} (H : t.Emb m T σ) (H' : t.Emb m T σ') {B : Type} [Field B]
    (y : Sp B ⟶ (T ⊗ t.A).left) {w} (h : SecCoord _ σ y w) : SecCoord _ σ' y w := by
  obtain ⟨th, s₁, α, U, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th', s₁', α', U', h₁', h₂', h₄', h₅', h₆'⟩ := H'
  have hL := t.isLB
  obtain ⟨c, hc⟩ := ThetaCoord.exists_unit_of_isGenSec h₁' h₁
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL p
  refine secCoord_of_sv hL p hI hI
    (val α' y p I * (val α y p I)⁻¹ * gm (y ≫ (fst T t.A).left) p ⊤ c) (fun a => ?_) h
  have e₀ : (U' a).pt = (U a).pt := (h₅' a).pt_eq.trans (h₅ a).pt_eq.symm
  have e₁ := val_corr hI (SymLiftOdd.symLift_unique hG t.ab hL hm.pow _ _ (h₅' a) (h₅ a)) y
  have f₁ : (y ≫ (translT t.A (U a).pt).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
  have f₂ : ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, mulT, lift_fst, f₁]
  have e₂ := CommPairing.val_div_eq hL (fst T t.A).left (CommPairing.surj_fst hG t.ab T) h₂' h₂ _ _ f₁ p I hI
  have e₃ := ThetaAct.sv_smul (c : Γ(T.left, ⊤)) (SecM.ofSec t.A th)
    ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) p hI
  rw [← hc, f₂, gs_unit _ _ ⊤ trivial] at e₃
  rw [VVRank.sv_of_isTwistPull t.A (h₆ a) y p hI, VVRank.sv_of_isTwistPull t.A (h₆' a) y p hI,
    VVRank.sv_of_isTwistPull t.A h₄ _ p hI, VVRank.sv_of_isTwistPull t.A h₄' _ p hI, ← e₂]
  erw [e₁]
  rw [e₀]
  rw [show VVRank.sv t.A th' _ p I = _ * VVRank.sv t.A th _ p I from e₃]
  simp only [Units.val_mul]
  have key : ∀ {Q : Type} [CommRing Q] (a a' : Qˣ) (x y z : Q), x * (a' * (y * z)) = a' * ↑a⁻¹ * y * (x * (a * z)) :=
    fun a a' x y z => by linear_combination (-(x * a' * y * z)) * a.inv_mul
  exact key _ _ _ _ _

end GlobalTheory.TUniq
