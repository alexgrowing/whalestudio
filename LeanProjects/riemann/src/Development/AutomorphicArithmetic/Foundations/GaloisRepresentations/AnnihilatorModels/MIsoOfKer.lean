import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

variable {S : Scheme.{0}}

private lemma pow_comp' {T A B : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  exact (IsMonHom.monoidHom f T).map_pow x n

private lemma comp_pow' {T' T A : Over S} [GrpObj A] (t : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    t ≫ (x ^ n) = (t ≫ x) ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => simp only [pow_succ, Hom.mul_def, comp_lift_assoc, ih]

private lemma self_pow {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    f ^ n = ((𝟙 A) ^ n) ≫ f := by
  rw [pow_comp', Category.id_comp]

private lemma cancel (hDiv : DivC) {A₀ A B : Over S} [GrpObj A₀] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {c : ℕ} (hc : 0 < c) (ψ : A₀ ⟶ A) (ψ' : A ⟶ A₀) (e : ψ' ≫ ψ = (𝟙 A) ^ c)
    (u v : A ⟶ B) [IsMonHom u] [IsMonHom v] (h : ψ ≫ u = ψ ≫ v) : u = v := by
  have h2 : ψ' ≫ ψ ≫ u = ψ' ≫ ψ ≫ v := by rw [h]
  rw [← Category.assoc, ← Category.assoc, e, ← self_pow, ← self_pow] at h2
  exact (hDiv S A B hA c hc).2 u v inferInstance inferInstance h2

private lemma factor (hDiv : DivC) {A₀ A₁ A₂ : Over S} [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₁] [IsCommMonObj A₁]
    [GrpObj A₂] [IsCommMonObj A₂] (h₀ : IsAbelianScheme A₀) (h₁ : IsAbelianScheme A₁) {c : ℕ} (hc : 0 < c)
    (ψ₁ : A₀ ⟶ A₁) (ψ₁' : A₁ ⟶ A₀) (ψ₂ : A₀ ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₁'] [IsMonHom ψ₂]
    (u : ψ₁ ≫ ψ₁' = (𝟙 A₀) ^ c) (v : ψ₁' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (g : T ⟶ A₀), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1) :
    ∃ ρ : A₁ ⟶ A₂, IsMonHom ρ ∧ ρ ^ c = ψ₁' ≫ ψ₂ ∧ ψ₁ ≫ ρ = ψ₂ := by
  obtain ⟨ν, hν, hνc⟩ := (hDiv S A₁ A₂ h₁ c hc).1 (ψ₁' ≫ ψ₂) inferInstance (by
    intro T g hg
    have : (g ≫ ψ₁') ≫ ψ₁ = 1 := by
      rw [Category.assoc, v, comp_pow', Category.comp_id, hg]
    rw [← Category.assoc]
    exact hk T _ this)
  haveI := hν
  refine ⟨ν, hν, hνc, ?_⟩
  refine (hDiv S A₀ A₂ h₀ c hc).2 (ψ₁ ≫ ν) ψ₂ inferInstance inferInstance ?_
  rw [← comp_pow', hνc, ← Category.assoc, u, ← self_pow]

variable {A T Y : Over S} [GrpObj A]

private lemma evc_pow_left {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (a : Y ⟶ A) (t : Y ⟶ T) (n : ℕ) :
    evc hM (a ^ n) t = n • evc hM a t := by
  induction n with
  | zero => simp [IsAdditive.evc_one hM h]
  | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hM).1 h, ih, succ_nsmul]

private lemma evc_add_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hP a (b * b') = evc hP a b + evc hP a b' := by
  have hs : (swap (A := A) (B := B) P).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hP _
  rw [← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs]
  exact (GlobalTheory.AbDual.isAdditive_iff hs).1 h Y b b' a

private lemma evc_pow_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hP a (b ^ n) = n • evc hP a b := by
  have hs : (swap (A := A) (B := B) P).IsLB := LB.isLB_pull hP _
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, ← GlobalTheory.AbDual.evc_swap hP hs]
    exact IsAdditive.evc_one hs h a
  | succ n ih => rw [pow_succ, evc_add_right hP h, ih, succ_nsmul]

end UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

open UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization in
theorem UpperTheory.Gal.crystallineComparison.Mod.isoOfKer_of :
    PairCalc → Adjoint → DivC → TorsFree → IsoOfKer := by
  intro hPC hAdj hDiv hTF
  intro p _ D R _ b N k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hker
  have hc : 0 < c := h1.pos
  obtain ⟨-, hm1, hact1, heta1, hpol1, ψ₁', hψ₁', u1, v1⟩ := h1
  obtain ⟨-, hm2, hact2, heta2, hpol2, ψ₂', hψ₂', u2, v2⟩ := h2
  haveI := hm1
  haveI := hm2
  haveI := hψ₁'
  haveI := hψ₂'
  obtain ⟨ρ, hρ, -, hρ1⟩ := factor hDiv o.ab o₁.ab hc ψ₁ ψ₁' ψ₂ u1 v1 (fun T g h => (hker T g).1 h)
  obtain ⟨ρ', hρ', -, hρ2⟩ := factor hDiv o.ab o₂.ab hc ψ₂ ψ₂' ψ₁ u2 v2 (fun T g h => (hker T g).2 h)
  haveI := hρ
  haveI := hρ'
  have hrr : ρ ≫ ρ' = 𝟙 o₁.A :=
    cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by rw [← Category.assoc, hρ1, hρ2, Category.comp_id])
  have hr'r : ρ' ≫ ρ = 𝟙 o₂.A :=
    cancel hDiv o₂.ab hc ψ₂ ψ₂' v2 _ _ (by rw [← Category.assoc, hρ2, hρ1, Category.comp_id])
  have hP0 := hPC p D R b N (Sp k) s o
  have hP1 := hPC p D R b N (Sp k) s o₁
  have hP2 := hPC p D R b N (Sp k) s o₂
  have e1 := (hP0.2.2.2.2 o₁ ψ₁ c).1 hpol1
  have e2 := (hP0.2.2.2.2 o₂ ψ₂ c).1 hpol2
  have hLp : (o₂.P.pull (sq2 ρ)).IsLB := LB.isLB_pull o₂.isLB _
  have hL : ((o₂.P.pull (sq2 ρ)).div o₁.P).IsLB := LB.isLB_div hLp o₁.isLB
  have hlift : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A), (lift a t).left ≫ sq2 ρ = (lift (a ≫ ρ) (t ≫ ρ)).left := by
    intro Y a t
    show (lift a t).left ≫ (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left = _
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have hevL : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A),
      evc hL a t = evc o₂.isLB (a ≫ ρ) (t ≫ ρ) - evc o₁.isLB a t := by
    intro Y a t
    unfold GlobalTheory.AbDual.evc
    rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, map_sub, GlobalTheory.CechPic.cls_pull o₂.isLB _ hLp,
      ← GlobalTheory.CechPic.pull_comp, hlift]
  have hadd1 := (GlobalTheory.AbDual.isAdditive_iff o₁.isLB).1 hP1.1
  have hadd2 := (GlobalTheory.AbDual.isAdditive_iff o₂.isLB).1 hP2.1
  have hmulρ : ∀ {Y : Over (Sp k)} (a a' : Y ⟶ o₁.A), (a * a') ≫ ρ = (a ≫ ρ) * (a' ≫ ρ) := by
    intro Y a a'
    exact (IsMonHom.monoidHom ρ Y).map_mul a a'
  have hLadd : IsAdditive ((o₂.P.pull (sq2 ρ)).div o₁.P) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hL]
    intro Y a a' t
    rw [hevL, hevL, hevL, hmulρ, hadd2, hadd1]
    abel
  have hsL : (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)).IsLB := LB.isLB_pull hL _
  have hLsadd : IsAdditive (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hsL]
    intro Y b' b'' a
    rw [GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, hevL, hevL, hevL, hmulρ,
      evc_add_right o₂.isLB hP2.2.1, evc_add_right o₁.isLB hP1.2.1]
    abel
  have hz : ∀ {Y : Over (Sp k)} (z w : Y ⟶ o.A), evc hL (z ≫ ψ₁) (w ≫ ψ₁) = 0 := by
    intro Y z w
    rw [hevL, Category.assoc, Category.assoc, hρ1, e1, e2, sub_self]
  have hxc : ∀ {Y : Over (Sp k)} (x : Y ⟶ o₁.A), x ^ c = (x ≫ ψ₁') ≫ ψ₁ := by
    intro Y x
    rw [Category.assoc, v1, comp_pow', Category.comp_id]
  have huniv : evc hL (fst o₁.A o₁.A) (snd o₁.A o₁.A) = GlobalTheory.CechPic.cls _ hL := by
    unfold GlobalTheory.AbDual.evc
    rw [lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have key : evc hL ((fst o₁.A o₁.A) ^ c) ((snd o₁.A o₁.A) ^ c) = 0 := by
    rw [hxc, hxc]
    exact hz _ _
  rw [evc_pow_left hL hLadd, evc_pow_right hL hLsadd, smul_smul, huniv] at key
  have hcls := hTF k o₁.A o₁.A o₁.ab o₁.ab _ hL hLadd hLsadd (c * c) (Nat.mul_pos hc hc) key
  rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, sub_eq_zero] at hcls
  have hpol : LBIso o₁.P (o₂.P.pull (sq2 ρ)) := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB hLp).1 hcls.symm
  haveI : IsIso ρ.left := ⟨⟨ρ'.left, by rw [← Over.comp_left, hrr, Over.id_left],
    by rw [← Over.comp_left, hr'r, Over.id_left]⟩⟩
  refine ⟨⟨ρ.left, sq2 ρ, ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩, ⟨?_, ?_⟩, ?_, hpol, ?_⟩, ?_⟩
  · intro T x y x₀ y₀ hx hy
    let i : Over.mk (T.hom ≫ 𝟙 (Sp k)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have hx' : x₀ = i ≫ x ≫ ρ := by
      ext1
      rw [hx]
      simp [i]
    have hy' : y₀ = i ≫ y ≫ ρ := by
      ext1
      rw [hy]
      simp [i]
    have hm : (i ≫ x ≫ ρ) * (i ≫ y ≫ ρ) = i ≫ (x * y) ≫ ρ := by
      rw [hmulρ x y, Hom.mul_def, Hom.mul_def, comp_lift_assoc]
    rw [hx', hy', hm]
    simp [i]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_fst, Over.comp_left]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  · intro a
    haveI := o₁.act.hom a
    haveI := o₂.act.hom a
    have h : o₁.act.act a ≫ ρ = ρ ≫ o₂.act.act a :=
      cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by
        rw [← Category.assoc, ← hact1 a, Category.assoc, hρ1, hact2 a, ← hρ1, Category.assoc])
    rw [← Over.comp_left, h, Over.comp_left]
  · intro y
    rw [← Over.comp_left, heta1 y, Category.assoc, hρ1, ← heta2 y, Category.id_comp]
  · rw [← Over.comp_left, hρ1]
