import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section RadialKernelIntegrals

variable {S : Scheme.{0}}

def precompHom {Y Y' G : Over S} [GrpObj G] (f : Y' ⟶ Y) : (Y ⟶ G) →* (Y' ⟶ G) :=
  MonoidHom.mk' (fun a => f ≫ a) (fun a b => MonObj.comp_mul f a b)

def postcompHom {Y G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (Y ⟶ G) →* (Y ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) (fun a b => MonObj.mul_comp a b g)

def evcHom {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hM a t)) (fun a b => by
    rw [(isAdditive_iff hM).1 h Y a b t]; rfl)

theorem evc_prod_zpow_left {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) {K : Type} [Fintype K] (a : K → (Y ⟶ A)) (n : K → ℤ) (t : Y ⟶ T) :
    evc hM (∏ k, a k ^ n k) t = ∑ k, n k • evc hM (a k) t := by
  have e := map_prod (evcHom hM h t) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact congrArg Multiplicative.toAdd e

theorem evc_pow_left {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) (a : Y ⟶ A) (n : ℕ) (t : Y ⟶ T) : evc hM (a ^ n) t = n • evc hM a t :=
  congrArg Multiplicative.toAdd (map_pow (evcHom hM h t) a n)

theorem evc_mul_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hM a (b * b') = evc hM a b + evc hM a b' := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', ← evc_swap hM hs', ← evc_swap hM hs']
  exact (isAdditive_iff hs').1 hs Y b b' a

theorem evc_prod_zpow_right {A B Y : Over S} [GrpObj B] [IsCommMonObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) {K : Type} [Fintype K] (a : Y ⟶ A) (b : K → (Y ⟶ B)) (n : K → ℤ) :
    evc hM a (∏ k, b k ^ n k) = ∑ k, n k • evc hM a (b k) := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_prod_zpow_left hs' hs]
  exact Finset.sum_congr rfl fun k _ => by rw [evc_swap hM hs']

theorem evc_pow_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hM a (b ^ n) = n • evc hM a b := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_pow_left hs' hs, evc_swap hM hs']

theorem comp_prod_zpow'' {Y Y' G : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K] (f : Y' ⟶ Y)
    (a : K → (Y ⟶ G)) (n : K → ℤ) : f ≫ ∏ k, a k ^ n k = ∏ k, (f ≫ a k) ^ n k := by
  have e := map_prod (precompHom f) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

theorem prod_zpow_comp'' {Y G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {K : Type}
    [Fintype K] (a : K → (Y ⟶ G)) (n : K → ℤ) (g : G ⟶ H) [IsMonHom g] :
    (∏ k, a k ^ n k) ≫ g = ∏ k, (a k ≫ g) ^ n k := by
  have e := map_prod (postcompHom (Y := Y) g) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

end RadialKernelIntegrals

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section KerAux2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [pa, ← Category.assoc, mkZ, lift_fst]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [pb, ← Category.assoc, mkZ, lift_snd]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (p q : Y ⟶ Zob A B) :
    CechPic.pull (lift p q).left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (p ≫ pa A B i) (q ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (p ≫ pa A B i) (q ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (q ≫ pa A B i) (p ≫ pb A B j)) +
      ∑ j, evc hQ (q ≫ pb A B j ≫ mu) (p ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

end KerAux2

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx j
  have hQ : IsDual c.A B Q := hZ.2.1
  have hQ' : IsDual B c.A (swap Q) := hZ.2.2.1
  haveI hla : IsMonHom la := hZ.2.2.2.1
  haveI hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hPQ := hZ.2.2.2.2.2.2.2
  have hzP := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
  have h0 : ∀ (Y : Over S) (s : Y ⟶ T) (z : Y ⟶ Zob c.A B),
      CechPic.pull (lift (s ≫ x) z).left (zCls c.A B c.isLB hQ.isLB d mu) = 0 := by
    intro Y s z
    have e := congrArg (CechPic.pull (lift z s).left) ((cls_eq_zero_iff (pull_isLB hzP _)).2 hx)
    rw [cls_pull hzP, cls_zP, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e
    exact e

  have e := h0 (c.A ⊗ T) (snd c.A T)
    (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then fst c.A T ≫ la else 1))
  rw [pull_zCls] at e
  simp only [mkZ_pa', mkZ_pb'] at e
  simp only [← Category.assoc, mkZ_pa', mkZ_pb'] at e
  have t2 : ∀ i, ∑ j', quat d j' i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i)
      (if j' = j then fst c.A T ≫ la else 1) = quat d j i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T ≫ la) :=
    fun i => by
      rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', evc_one_right hQ.isLB hQ.zero, smul_zero]),
        if_pos rfl]
  have t4 : ∑ j', evc hQ.isLB ((if j' = j then fst c.A T ≫ la else 1) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j') =
      evc hQ.isLB ((fst c.A T ≫ la) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', MonObj.one_comp, hQ.additive.evc_one hQ.isLB]),
      if_pos rfl]
  simp only [t2, t4, evc_one_right c.isLB c.rig₂, hQ.additive.evc_one hQ.isLB, smul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at e
  have hPev : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc hQ.isLB p (q ≫ la) := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc hQ.isLB (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ.isLB _)).2 hPQ
    rw [evc, e1, pull_evc, lift_fst, lift_snd_assoc]
  have hPsymm : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc c.isLB q p := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    rw [evc, e1, pull_evc, lift_fst, lift_snd]
  have hQsw : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc hQ.isLB p (q ≫ la) = evc hQ.isLB q (p ≫ la) := by
    intro Y p q
    rw [← hPev, ← hPev, hPsymm]
  refine (hQ.isPerfect hQ').ker_right T _ ((triv_ev_iff hQ.isLB _ _).2 ?_)
  rw [MonObj.comp_mul, ← Category.assoc, comp_prod_zpow'', prod_zpow_comp'', MonObj.comp_pow,
    evc_mul_right hQ.isLB hQ'.additive, evc_prod_zpow_right hQ.isLB hQ'.additive, evc_pow_right hQ.isLB hQ'.additive]
  rw [Category.assoc, hlm, MonObj.comp_pow, Category.comp_id, evc_pow_left hQ.isLB hQ.additive] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQsw, Category.assoc]

end GlobalTheory.ZarhinKerB
