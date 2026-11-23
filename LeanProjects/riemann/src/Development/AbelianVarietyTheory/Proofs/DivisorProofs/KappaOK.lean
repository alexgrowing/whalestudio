import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam

def sig : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

def oMat (d : ℕ) (k : Fin 8) : ord d :=
  ⟨Matrix.single (Sum.inl 0) (sig k) 1, fun i j => by simp [Matrix.single]⟩

def jlMap (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) where
  toFun a := fun
    | .inl i => if hi : (i : ℕ) < h then a (.inl ⟨i, hi⟩) else 0
    | .inr i => if hi : (i : ℕ) < h then a (.inr ⟨i, hi⟩) else 0
  map_zero' := by
    funext i; rcases i with i | i <;> simp
  map_add' a b := by
    funext i; rcases i with i | i <;> simp only [Pi.add_apply] <;> split_ifs <;> simp

def formZ (d h : ℕ) (X Y : Fin 8 → Fin h ⊕ Fin h → ℤ) : ℤ :=
  ∑ k, ∑ l, form d (sig k) (sig l) * omegaStd (X k) (Y l)

def KappaOK (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) : Prop :=
  (∀ a b, formZ d h (fun k => κ k a) (fun k => κ k b) ≡ omegaStd a b [ZMOD (M : ℤ)]) ∧
    (∀ a, κ 0 (jlMap h a) = a) ∧ ∀ k, k ≠ 0 → ∀ a, κ k (jlMap h a) = 0

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Zob : Over S := Out.powObj A 4 ⊗ Out.powObj B 4

def pa (i : Fin 4) : Zob A B ⟶ A := fst _ _ ≫ Out.powPr A i

def pb (j : Fin 4) : Zob A B ⟶ B := snd _ _ ≫ Out.powPr B j

def mkZ {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) : T ⟶ Zob A B :=
  lift ((Out.powIsLimit A 4).lift (Fan.mk T u)) ((Out.powIsLimit B 4).lift (Fan.mk T v))

def actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) : Zob A B ⟶ Zob A B :=
  mkZ A B
    (fun i => ∏ j, (pa A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i)) *
      (pb A B j ≫ mu) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))))
    (fun i => ∏ j, ((pa A B j ≫ la) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i)) *
      pb A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))))

def incZ : A ⟶ Zob A B := mkZ A B (fun i => if i = 0 then 𝟙 A else 1) (fun _ => 1)

def prZ : Zob A B ⟶ A := pa A B 0

def zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    Pic (Zob A B ⊗ Zob A B).left :=
  (∑ i, pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pa A B i)).left
      (cls P hP)) +
    (∑ i, ∑ j, quat d j i • pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i)
      (snd (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    (∑ i, ∑ j, quat d j i • pull (lift (snd (Zob A B) (Zob A B) ≫ pa A B i)
      (fst (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    ∑ j, pull (lift (snd (Zob A B) (Zob A B) ≫ pb A B j ≫ mu) (fst (Zob A B) (Zob A B) ≫ pb A B j)).left
      (cls Q hQ)

def zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    LB (Zob A B ⊗ Zob A B).left :=
  (cls_surj (zCls A B hP hQ d mu)).choose

theorem zarhinBundle_isLineBundle {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    (zP A B hP hQ d mu).IsLB :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose

theorem cls_zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    cls (zP A B hP hQ d mu) (zarhinBundle_isLineBundle A B hP hQ d mu) = zCls A B hP hQ d mu :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose_spec

end Obj

def levZ {S : Scheme.{0}} {A Z : Over S} [GrpObj Z] [IsCommMonObj Z] {O : Type} {h h' n : ℕ}
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (inc : A ⟶ Z) (act : O → (Z ⟶ Z)) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) : 𝟙_ (Over S) ⟶ Z :=
  (List.ofFn fun k => lev (κ k a) ≫ inc ≫ act (o k)).prod

def ZData {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t) (d : ℕ)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) : Prop :=
  IsAbelianScheme B ∧ IsDual c.A B Q ∧ IsDual B c.A (swap Q) ∧ IsMonHom la ∧ IsMonHom mu ∧
    la ≫ mu = 𝟙 c.A ^ d ∧ mu ≫ la = 𝟙 B ^ d ∧ LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))

end GlobalTheory.ZarhinFam
