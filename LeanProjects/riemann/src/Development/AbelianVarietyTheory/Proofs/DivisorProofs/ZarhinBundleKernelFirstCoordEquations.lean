import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinKerA

variable {S : Scheme.{0}}

theorem mkZ_pa' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) : mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) : mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem pull_zCls {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (w ≫ pa A B i) (w' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w ≫ pa A B i) (w' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w' ≫ pa A B i) (w ≫ pb A B j)) +
      ∑ j, evc hQ (w' ≫ pb A B j ≫ mu) (w ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx i
  have hP := c.isLB
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hQd : IsDual c.A B Q := hZ.2.1
  have hQd' : IsDual B c.A (swap Q) := hZ.2.2.1
  have hs : (swap Q).IsLB := hQd'.isLB
  haveI : IsMonHom mu := hZ.2.2.2.2.1

  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _
      (pull_isLB (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _)]
    exact (cls_eq_zero_iff _).2 hx

  let inc : c.A ⟶ Zob c.A B := mkZ c.A B (fun k => if k = i then 𝟙 c.A else 1) (fun _ => 1)
  have h1 := congrArg (CechPic.pull (lift (fst c.A T ≫ inc) (snd c.A T)).left) h0
  rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst, pull_zCls] at h1
  have hpa : ∀ k, (fst c.A T ≫ inc) ≫ pa c.A B k = if k = i then fst c.A T else 1 := by
    intro k
    rw [Category.assoc, mkZ_pa']
    split_ifs <;> simp [MonObj.comp_one]
  have hpb : ∀ j, (fst c.A T ≫ inc) ≫ pb c.A B j = 1 := by
    intro j
    rw [Category.assoc, mkZ_pb', MonObj.comp_one]
  have z1 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hP a (1 : Y ⟶ c.A) = 0 := fun a => evc_one_right hP c.rig₂ a
  have z2 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hQ a (1 : Y ⟶ B) = 0 := fun a => evc_one_right hQ hQd.zero a
  have z3 : ∀ {Y : Over S} (b : Y ⟶ B), evc hQ (1 : Y ⟶ c.A) b = 0 := fun b => hQd.additive.evc_one hQ b
  have s1 : (∑ k, evc hP ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pa c.A B k)) =
      evc hP ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hpa, if_neg hk, z1]) (fun hi => absurd (Finset.mem_univ i) hi),
      hpa, if_pos rfl]
  have s2 : (∑ k, ∑ j, quat d j k • evc hQ ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pb c.A B j)) = 0 := by
    simp only [hpb, z2, smul_zero, Finset.sum_const_zero]
  have s3 : (∑ k, ∑ j, quat d j k • evc hQ ((fst c.A T ≫ inc) ≫ pa c.A B k) ((snd c.A T ≫ x) ≫ pb c.A B j)) =
      ∑ j, quat d j i • evc hQ (fst c.A T) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp only [hpa, if_neg hk, z3, smul_zero, Finset.sum_const_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hpa, if_pos rfl]
  have s4 : (∑ j, evc hQ ((fst c.A T ≫ inc) ≫ pb c.A B j ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j)) = 0 := by
    simp only [← Category.assoc _ (pb c.A B _) mu, hpb, MonObj.one_comp, z3, Finset.sum_const_zero]
  rw [s1, s2, s3, s4, add_zero, add_zero] at h1

  have eS : cls c.P hP = evc hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
  have eL : cls c.P hP = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff hP (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  have ePQ : ∀ {Y : Over S} (u a : Y ⟶ c.A), evc hP u a = evc hQ a (u ≫ la) := by
    intro Y u a
    have e1 := congrArg (CechPic.pull (lift u a).left) eS
    have e2 := congrArg (CechPic.pull (lift a u).left) eL
    rw [pull_evc, lift_snd, lift_fst] at e1
    rw [pull_evc, lift_fst, lift_snd_assoc] at e2
    exact e1.trans e2

  have hadd : ∀ {Y : Over S} (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    rw [← evc_swap hQ hs, ← evc_swap hQ hs, ← evc_swap hQ hs]
    exact (isAdditive_iff hs).1 hQd'.additive Y b b' a
  let φ : (T ⟶ B) →* Multiplicative (Pic (c.A ⊗ T).left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hQ (fst c.A T) (snd c.A T ≫ b))) fun b b' => by
      simp only [MonObj.comp_mul, hadd, ofAdd_add]
  refine (hQd.isPerfect hQd').ker_right T _ ((triv_ev_iff hQ _ _).2 ?_)
  have key : Multiplicative.toAdd (φ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) =
      evc hQ (fst c.A T) (snd c.A T ≫ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) := rfl
  rw [← key, map_mul, map_prod, toAdd_mul, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, φ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [← Category.assoc, ← Category.assoc, ← ePQ]
  simpa only [Category.assoc] using h1

end GlobalTheory.ZarhinKerA
