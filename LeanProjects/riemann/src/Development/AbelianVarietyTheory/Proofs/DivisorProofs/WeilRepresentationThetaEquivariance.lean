import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKerStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinExist

section Dual

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Q : LB (A ⊗ B).left}

theorem evc_mul_right (hQ' : IsDual B A (swap Q)) (hQ : Q.IsLB) {Y : Over S} (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
  have e := (isAdditive_iff hQ'.isLB).1 hQ'.additive Y b b' a
  rwa [evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB] at e

theorem eq_of_evc (hQ : IsDual A B Q) {T : Over S} (x y : T ⟶ B)
    (h : evc hQ.isLB (fst A T) (snd A T ≫ x) = evc hQ.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev Q (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hQ.isLB _
  have hadd : IsAdditive (ev Q (fst A T) (snd A T ≫ x)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t => ?_
    rw [evc_ev hQ.isLB, evc_ev hQ.isLB, evc_ev hQ.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hQ.isLB).1 hQ.additive Y a a' (t ≫ x)
  refine (hQ.univ T _ hM hadd).unique ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hQ.isLB _)).1 ?_)
  rw [cls_ev hQ.isLB, cls_ev hQ.isLB]
  exact h

end Dual

section Siegel

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)

theorem evc_mul_left (hA : Out.RelAmple c.A c.diag) {Y : Over S} (a a' b : Y ⟶ c.A) :
    evc c.isLB (a * a') b = evc c.isLB a b + evc c.isLB a' b :=
  GlobalTheory.PrincipalIntegral.pair_mul c GlobalTheory.SemiRigid.globalFns hA Y a a' b

theorem evc_comm {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc c.isLB b a :=
  GlobalTheory.PrincipalIntegral.pair_comm c Y a b

theorem isAdditive_P (hA : Out.RelAmple c.A c.diag) : IsAdditive c.P :=
  (isAdditive_iff c.isLB).2 fun _ a a' b => evc_mul_left c hA a a' b

variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem evc_la (hQ : Q.IsLB) {la : c.A ⟶ B} (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la)))
    {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc hQ a (b ≫ la) := by
  have e := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff c.isLB (pull_isLB hQ _)).2 hla)
  rw [cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc] at e
  exact e

end Siegel

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

section Main

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem isMonHom_la (hA : Out.RelAmple c.A c.diag) (hQ : IsDual c.A B Q) (hQ' : IsDual B c.A (swap Q)) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) : IsMonHom la := by
  refine isMonHom_of_mul la fun T x y => eq_of_evc hQ _ _ ?_
  rw [← Category.assoc, ← evc_la c hQ.isLB hla, comp_mul, comp_mul, evc_mul_right hQ' hQ.isLB, ← Category.assoc,
    ← Category.assoc, ← evc_la c hQ.isLB hla, ← evc_la c hQ.isLB hla,
    evc_comm c (fst c.A T) ((snd c.A T ≫ x) * (snd c.A T ≫ y)), evc_mul_left c hA, evc_comm c _ (fst c.A T),
    evc_comm c _ (fst c.A T)]

theorem pow_eq_one_of_la {d : ℕ} (hK : SiegKerBy c d) (hQ : IsDual c.A B Q) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) {T : Over S} (x : T ⟶ c.A) (hx : x ≫ la = 1) :
    x ^ d = 1 := by
  refine hK.2 T x ((cls_eq_zero_iff (pull_isLB c.isLB _)).1 ?_)
  change evc c.isLB (snd c.A T ≫ x) (fst c.A T) = 0
  rw [evc_comm c, evc_la c hQ.isLB hla, Category.assoc, hx, MonObj.comp_one, evc_one_right hQ.isLB hQ.zero]

end Main

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

open GlobalTheory.ZarhinFam

theorem exists_zData : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  intro h M d S t c _ _ _ hd _ _ hK
  obtain ⟨B, iB, Q, hB, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme S c.A c.ab
  obtain ⟨la, hla, -⟩ := hQ.univ c.A c.P c.isLB (isAdditive_P c hK.1)
  have hmon := isMonHom_la c hK.1 hQ hQ' hla
  obtain ⟨mu, hmu, h1, h2⟩ := GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker S c.A B Q la d c.ab hB hQ hQ' hmon hd
    fun T x hx => pow_eq_one_of_la c hK hQ hla x hx
  exact ⟨B, iB, hB.comm, Q, la, mu, hB, hQ, hQ', hmon, hmu, h1, h2, hla⟩

end GlobalTheory.ZarhinExist
