import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

def zm (F : Coef C) : C ⥤ ModuleCat.{1} ℤ where
  obj A := ModuleCat.of ℤ (F.obj A)
  map φ := ModuleCat.ofHom (F.map φ).hom.toIntLinearMap
  map_id A := by ext x; simp
  map_comp φ ψ := by ext x; simp

def zmMap {F G : Coef C} (α : F ⟶ G) : zm F ⟶ zm G where
  app A := ModuleCat.ofHom (α.app A).hom.toIntLinearMap
  naturality A B φ := by
    ext x
    exact congrArg (fun f => f.hom x) (α.naturality φ)

abbrev TH (P : C ⥤ Type) (F : Coef C) (j : ℕ) : Type 1 := CH.H (elF P (zm F)) j

def tPull {Q P : C ⥤ Type} (u : Q ⟶ P) (F : Coef C) (j : ℕ) : TH P F j →+ TH Q F j :=
  ((elMor u (zm F)).pull j).toAddMonoidHom

def tMap (P : C ⥤ Type) {F G : Coef C} (α : F ⟶ G) (j : ℕ) : TH P F j →+ TH P G j :=
  ((elCoef P (zmMap α)).pull j).toAddMonoidHom

theorem tPull_tMap {Q P : C ⥤ Type} (u : Q ⟶ P) {F G : Coef C} (α : F ⟶ G) (j : ℕ) (x : TH P F j) :
    tPull u G j (tMap P α j x) = tMap Q α j (tPull u F j x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm F))) j).1 x
  rfl

theorem ses_app (S : ShortComplex (Coef C)) (h : S.ShortExact) :
    (∀ A, Function.Injective (S.f.app A).hom) ∧ (∀ A, Function.Exact (S.f.app A).hom (S.g.app A).hom) ∧
      ∀ A, Function.Surjective (S.g.app A).hom := by
  have := h.mono_f
  have := h.epi_g
  refine ⟨fun A => ?_, fun A => ?_, fun A => ?_⟩
  · exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance A)
  · have := (h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj A)).exact
    exact (ShortComplex.ab_exact_iff_function_exact _).1 this
  · exact (AddCommGrpCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 inferInstance A)

theorem les_ex (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) :
    ∃ δ : ∀ n, TH P S.X₃ n →ₗ[ℤ] TH P S.X₁ (n + 1),
      (∀ n (y : (cx (elF P (zm S.X₂))).X n) (x : (cx (elF P (zm S.X₁))).X (n + 1)) hz hx,
        (elCoef P (zmMap S.f)).hom.f (n + 1) x = (cx (elF P (zm S.X₂))).d n y →
          δ n ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f n y) hz) = (cx (elF P (zm S.X₁))).cls x hx) ∧
      Function.Injective ((elCoef P (zmMap S.f)).hom.mapH 0) ∧
      (∀ n, Function.Exact ((elCoef P (zmMap S.f)).hom.mapH n) ((elCoef P (zmMap S.g)).hom.mapH n)) ∧
      (∀ n, Function.Exact ((elCoef P (zmMap S.g)).hom.mapH n) (δ n)) ∧
      ∀ n, Function.Exact (δ n) ((elCoef P (zmMap S.f)).hom.mapH (n + 1)) := by
  obtain ⟨hi, he, hs⟩ := ses_app S h
  obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.f))
    (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))
    (fun T => hi T.1) (fun T => he T.1) (fun T => hs T.1)
  exact CrystallineSemistableComparison.P.les _ _ h1 h2 h3

def tδ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) : TH P S.X₃ j →+ TH P S.X₁ (j + 1) :=
  (Classical.choose (les_ex P S h) j).toAddMonoidHom

theorem tδ_spec (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (n : ℕ)
    (y : (cx (elF P (zm S.X₂))).X n) (x : (cx (elF P (zm S.X₁))).X (n + 1)) (hz) (hx)
    (e : (elCoef P (zmMap S.f)).hom.f (n + 1) x = (cx (elF P (zm S.X₂))).d n y) :
    tδ P S h n ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f n y) hz) = (cx (elF P (zm S.X₁))).cls x hx :=
  (Classical.choose_spec (les_ex P S h)).1 n y x hz hx e

theorem ex₃ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) :
    Function.Exact (tMap P S.g j) (tδ P S h j) :=
  (Classical.choose_spec (les_ex P S h)).2.2.2.1 j

theorem ex₁ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) :
    Function.Exact (tδ P S h j) (tMap P S.f (j + 1)) :=
  (Classical.choose_spec (les_ex P S h)).2.2.2.2 j

theorem tPull_tδ {Q P : C ⥤ Type} (u : Q ⟶ P) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) (x : TH P S.X₃ j) :
    tPull u S.X₁ (j + 1) (tδ P S h j x) = tδ Q S h j (tPull u S.X₃ j x) := by
  obtain ⟨hi, he, hs⟩ := ses_app S h
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm S.X₃))) j).1 x
  obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.f))
    (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))
    (fun T => hi T.1) (fun T => he T.1) (fun T => hs T.1)
  obtain ⟨y, rfl⟩ := h3 j c
  have hdy : (Mor.ofNatTrans (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))).hom.f (j + 1)
      ((cx (elF P (zm S.X₂))).d j y) = 0 := by
    rw [← Cx.Hom.comm]; exact hc
  obtain ⟨x, hx⟩ := ((h2 (j + 1)) _).1 hdy
  have hxz : (cx (elF P (zm S.X₁))).d (j + 1) x = 0 := by
    apply h1 (j + 1 + 1)
    rw [map_zero, ← Cx.Hom.comm, hx]
    exact (cx (elF P (zm S.X₂))).dd j y
  have e1 : tPull u S.X₃ j ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f j y) hc) =
      (cx (elF Q (zm S.X₃))).cls ((elCoef Q (zmMap S.g)).hom.f j ((elMor u (zm S.X₂)).hom.f j y))
        (by
          exact ((elMor u (zm S.X₃)).hom.comm j ((elCoef P (zmMap S.g)).hom.f j y)).trans
            ((congrArg _ hc).trans (map_zero _))) := rfl
  have e2 : tPull u S.X₁ (j + 1) ((cx (elF P (zm S.X₁))).cls x hxz) =
      (cx (elF Q (zm S.X₁))).cls ((elMor u (zm S.X₁)).hom.f (j + 1) x) (by
        rw [Cx.Hom.comm, hxz, map_zero]) := rfl
  refine (congrArg (tPull u S.X₁ (j + 1)) (tδ_spec P S h j y x hc hxz hx)).trans ?_
  refine e2.trans (Eq.trans ?_ (congrArg (tδ Q S h j) e1).symm)
  refine (tδ_spec Q S h j _ _ _ _ ?_).symm
  refine Eq.trans ?_ ((elMor u (zm S.X₂)).hom.comm j y).symm
  exact congrArg ((elMor u (zm S.X₂)).hom.f (j + 1)) hx

end UpperTheory.Ru.crystallineComparison.Th
