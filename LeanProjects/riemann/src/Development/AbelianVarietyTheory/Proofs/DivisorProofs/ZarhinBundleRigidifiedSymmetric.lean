import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEqStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.Rig

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem pull_pull_lift {Y W X₁ X₂ : Over S} {M : LB (X₁ ⊗ X₂).left} (hM : M.IsLB) (u : Y ⟶ W) (f : W ⟶ X₁)
    (g : W ⟶ X₂) : CechPic.pull u.left (CechPic.pull (lift f g).left (cls M hM)) = evc hM (u ≫ f) (u ≫ g) := by
  rw [← pull_comp, ← Over.comp_left, comp_lift]; rfl

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (z z' : Y ⟶ Zob A B) :
    CechPic.pull (lift z z').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (z ≫ pa A B i) (z' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z ≫ pa A B i) (z' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z' ≫ pa A B i) (z ≫ pb A B j)) +
      ∑ j, evc hQ (z' ≫ pb A B j ≫ mu) (z ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, pull_pull_lift, lift_fst_assoc, lift_snd_assoc]

theorem zarhinBundle_pull_trivial_iff {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ)
    (mu : B ⟶ A) {Y : Over S} (u : Y ⟶ Zob A B ⊗ Zob A B) :
    (∃ t : ((zP A B hP hQ d mu).pull u.left).Gen, t.IsGen) ↔
      CechPic.pull u.left (zCls A B hP hQ d mu) = 0 := by
  rw [← cls_eq_zero_iff (pull_isLB (zarhinBundle_isLineBundle A B hP hQ d mu) _), cls_pull (zarhinBundle_isLineBundle A B hP hQ d mu), cls_zP]

theorem one_pa {Y : Over S} (i : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pa A B i = 1 := by
  simp [pa]

theorem one_pb {Y : Over S} (j : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pb A B j = 1 := by
  simp [pb]

theorem one_pb_assoc {Y X : Over S} (j : Fin 4) (f : B ⟶ X) : (1 : Y ⟶ Zob A B) ≫ pb A B j ≫ f = 1 ≫ f := by
  rw [← Category.assoc, one_pb]

end

section Sym
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem evc_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Y : Over S} (a a' : Y ⟶ A) : evc hP a a' = evc hP a' a := by
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) := (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hPs
  change CechPic.pull (lift a a').left (cls P hP) = _
  rw [e₁, pull_evc, lift_snd, lift_fst]

theorem evc_mu_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Q : LB (A ⊗ B).left} (hQ : IsDual A B Q) (hQ' : IsDual B A (swap Q)) {d : ℕ} {la : A ⟶ B} {mu : B ⟶ A}
    (hmu : IsMonHom mu) (hlm : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d)
    (hPQ : LBIso P (ev Q (fst A A) (snd A A ≫ la)))
    (htor : ∀ x y : B ⟶ A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y)
    {Y : Over S} (b b' : Y ⟶ B) : evc hQ.isLB (b' ≫ mu) b = evc hQ.isLB (b ≫ mu) b' := by
  have hQl := hQ.isLB
  have hs := hQ'.isLB
  have addL : ∀ (Y : Over S) (a a' : Y ⟶ A) (b : Y ⟶ B), evc hQl (a * a') b = evc hQl a b + evc hQl a' b :=
    (isAdditive_iff hQl).1 hQ.additive
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hQl a (b * b') = evc hQl a b + evc hQl a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 hQ'.additive Y b b' a
    rwa [evc_swap hQl hs, evc_swap hQl hs, evc_swap hQl hs] at k
  have powL : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl (a ^ n) b = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hQ.additive.evc_one hQl b
    | succ n ih => rw [pow_succ, addL, ih, succ_nsmul]
  have powR : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl a (b ^ n) = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQl hQ.zero a
    | succ n ih => rw [pow_succ, addR, ih, succ_nsmul]
  have PQ : ∀ (Y : Over S) (a a' : Y ⟶ A), evc hP a a' = evc hQl a (a' ≫ la) := by
    intro Y a a'
    have e₂ : cls P hP = evc hQl (fst A A) (snd A A ≫ la) := (CechPic.cls_eq_iff hP (pull_isLB hQl _)).2 hPQ
    change CechPic.pull (lift a a').left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]

  let Mb : LB (B ⊗ B).left := ev Q (fst B B ≫ mu) (snd B B)
  have hM : Mb.IsLB := pull_isLB hQl _
  have evcM : ∀ (Y : Over S) (b t : Y ⟶ B), evc hM b t = evc hQl (b ≫ mu) t := by
    intro Y b t
    rw [evc_ev hQl, lift_fst_assoc, lift_snd]
  have haM : IsAdditive Mb := (isAdditive_iff hM).2 fun Y b b' t => by
    rw [evcM, evcM, evcM, MonObj.mul_comp, addL]
  obtain ⟨x, hx, -⟩ := hQ'.univ B Mb hM haM
  have K : ∀ (Y : Over S) (b t : Y ⟶ B), evc hQl (b ≫ mu) t = evc hQl (t ≫ x) b := by
    intro Y b t
    have c := (CechPic.cls_eq_iff hM (pull_isLB hs _)).2 hx
    have k : evc hM b t = evc (pull_isLB hs _) b t := congrArg (CechPic.pull (lift b t).left) c
    rw [evc_ev hs, lift_fst, lift_snd_assoc, evc_swap hQl hs, evcM] at k
    exact k
  have hss : (swap (swap Q)).IsLB := pull_isLB hs _
  have ha' : IsAdditive (swap (swap Q)) := (isAdditive_iff hss).2 fun Y a a' t => by
    simp only [evc_swap hs hss, evc_swap hQl hs]; exact addL Y a a' t
  have hsM : (swap Mb).IsLB := pull_isLB hM _
  have haSM : IsAdditive (swap Mb) := (isAdditive_iff hsM).2 fun Y t t' b => by
    simp only [evc_swap hM hsM, evcM]; exact addR Y _ t t'
  have hxm : IsMonHom x := isMonHom_of_classifying S B B A Mb (swap Q) hQ' ha' hM haSM x hx
  have key : ∀ (Y : Over S) (b : Y ⟶ B) (a : Y ⟶ A), evc hQl (a ≫ la ≫ x) b = evc hQl (a ≫ la ≫ mu) b := by
    intro Y b a
    rw [← Category.assoc a la x, ← K, ← PQ, evc_symm hP hPs, PQ, Category.assoc, hml, hlm, comp_pow,
      Category.comp_id, comp_pow, Category.comp_id, powR, powL]
  have lx : la ≫ x = la ≫ mu := by
    apply hQ'.eq_of_evc
    rw [evc_swap hQl hs, evc_swap hQl hs, key]
  have xd : x ^ d = mu ^ d := by
    have e₁ : (𝟙 B ^ d) ≫ x = x ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    have e₂ : (𝟙 B ^ d) ≫ mu = mu ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    rw [← e₁, ← e₂, ← hml, Category.assoc, lx, ← Category.assoc]
  have xm : x = mu := htor x mu hxm hmu xd
  rw [K, xm]

end Sym

theorem zarhinBundle_rigidified_symmetric₂ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hdu _
  have hQ := hZ.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  refine ⟨(zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, (zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, ?_⟩
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_left c.isLB c.rig₁,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_right c.isLB c.rig₂,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
    refine (CechPic.cls_eq_iff hz (pull_isLB hz _)).1 ?_
    rw [cls_pull hz, cls_zP]
    conv_lhs => rw [← pull_id (zCls _ _ _ _ _ _), ← Over.id_left, ← lift_fst_snd]
    rw [pull_zCls, pull_zCls]
    have htor : ∀ x y : B ⟶ c.A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y :=
      GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq S c.A B c.ab hZ.1 d hd hdu
    have h1 : ∑ i, evc c.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) =
        ∑ i, evc c.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) :=
      Finset.sum_congr rfl fun i _ => evc_symm c.isLB c.symm _ _
    have h4 : ∑ j, evc hQ.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) =
        ∑ j, evc hQ.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) :=
      Finset.sum_congr rfl fun j _ => by
        simpa only [Category.assoc] using evc_mu_symm c.isLB c.symm hQ hZ.2.2.1 hZ.2.2.2.2.1 hZ.2.2.2.2.2.1
          hZ.2.2.2.2.2.2.1 hZ.2.2.2.2.2.2.2 htor (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j)
    rw [h1, h4]
    abel

end GlobalTheory.ZarhinFam.Rig
