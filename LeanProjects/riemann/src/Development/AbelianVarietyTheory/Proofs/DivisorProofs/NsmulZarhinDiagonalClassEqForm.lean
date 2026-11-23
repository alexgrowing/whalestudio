import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_comp_idPow {S : Scheme.{0}} {B Y : Over S} [GrpObj B] (b : Y ⟶ B) (n : ℕ) :
    b ≫ (𝟙 B) ^ n = b ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem zClsDiag_nsmul_evc {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B]
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hs : IsDual B A (swap Q)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    n • evc hQ a b = evc hQ a (b ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ← evc_swap hQ hs.isLB, hs.additive.evc_one hs.isLB]
  | succ n ih =>
    rw [succ_nsmul, ih, pow_succ, ← evc_swap hQ hs.isLB (b ^ n * b), (isAdditive_iff hs.isLB).1 hs.additive,
      evc_swap hQ hs.isLB, evc_swap hQ hs.isLB]

theorem zClsDiag_key {h M d : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
    {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (c.A ⊗ B).left} {la : c.A ⟶ B} {mu : B ⟶ c.A}
    (hZ : ZData c d B Q la mu) {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B) :
    d • pull (lift a b).left (cls Q hZ.2.1.isLB) = pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := by
  have hQ := hZ.2.1.isLB
  have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  show d • evc hQ a b = _
  rw [e, pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hZ.2.2.2.2.2.2.1, zClsDiag_comp_idPow,
    zClsDiag_nsmul_evc hQ hZ.2.2.1]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_sum_sig {M : Type*} [AddCommMonoid M] (F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → M) :
    ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) = ∑ s, ∑ t, F s t := by
  let e : Fin 8 ≃ Fin 4 ⊕ Fin 4 := Equiv.ofBijective sig (by decide)
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun k _ => Equiv.sum_comp e (F (sig k))).trans (Equiv.sum_comp e fun s => ∑ t, F s t)

theorem nsmul_pull_diag_zCls : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ _
  let F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Pic (Zob c.A B).left := fun s u =>
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 s u •
      pull (lift (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) s)
        (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) u)).left (cls c.P c.isLB)
  rw [show (∑ kl : Fin 8 × Fin 8, zW d kl.1 kl.2 • pull (lift (zpr c.A B mu kl.1) (zpr c.A B mu kl.2)).left
      (cls c.P c.isLB)) = ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) from rfl, zClsDiag_sum_sig]
  simp only [F, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]
  simp only [zCls, map_add, map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp]
  have hk : ∀ {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B), d • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun a b => zClsDiag_key c hZ a b
  have hk' : ∀ {Y : Over S} (z : ℤ) (a : Y ⟶ c.A) (b : Y ⟶ B), d • z • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      z • pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun z a b => by rw [smul_comm, hk]
  simp only [smul_add, Finset.smul_sum, hk, hk', Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
    zero_add, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, one_smul, Finset.sum_add_distrib, mul_smul, two_smul, natCast_zsmul]
  abel

end GlobalTheory.ZarhinFam
