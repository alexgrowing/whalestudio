import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem lamBC_psum_hom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)

theorem lamBC_psum_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (I : Finset (Fin n)) :
    (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (lamBC_psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (lamBC_psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

theorem lamEq_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  intro S S' s X Y A B X' Y' A' B' _ _ _ _ x y a b hx hy hA hB L M L' M' hL hM hL' hM' iL iM
    f₁ f₂ g₁ g₂ f₁' f₂' g₁' g₂' e₁ e₂ e₃ e₄ H
  let p : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X := Over.homMk ((fst X' Y').left ≫ x) (by
    show ((fst X' Y').left ≫ x) ≫ X.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hx, ← Category.assoc, Over.w])
  let q : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ Y := Over.homMk ((snd X' Y').left ≫ y) (by
    show ((snd X' Y').left ≫ y) ≫ Y.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hy, ← Category.assoc, Over.w])
  let U : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X ⊗ Y := lift p q
  have key : ∀ {C : Over S} {C' : Over S'} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C s c) (u : X ⟶ C) (v : Y ⟶ C) (u' : X' ⟶ C') (v' : Y' ⟶ C'),
      u'.left ≫ c = x ≫ u.left → v'.left ≫ c = y ≫ v.left → ∀ I : Finset (Fin 2),
      (psum C' ![fst X' Y' ≫ u', snd X' Y' ≫ v'] I).left ≫ c =
        U.left ≫ (psum C ![fst X Y ≫ u, snd X Y ≫ v] I).left := by
    intro C C' _ _ c hC u v u' v' hu hv I
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I
    fin_cases i
    · show pushPt hC.1.w (fst X' Y' ≫ u') = lift p q ≫ fst X Y ≫ u
      rw [lift_fst_assoc]
      refine Over.OverMorphism.ext ?_
      show ((fst X' Y').left ≫ u'.left) ≫ c = ((fst X' Y').left ≫ x) ≫ u.left
      rw [Category.assoc, hu, Category.assoc]
    · show pushPt hC.1.w (snd X' Y' ≫ v') = lift p q ≫ snd X Y ≫ v
      rw [lift_snd_assoc]
      refine Over.OverMorphism.ext ?_
      show ((snd X' Y').left ≫ v'.left) ≫ c = ((snd X' Y').left ≫ y) ≫ v.left
      rw [Category.assoc, hv, Category.assoc]
  have H₁ : LBIso (cubeLB A' ![fst X' Y' ≫ f₁', snd X' Y' ≫ f₂'] (L.pull a))
      (cubeLB B' ![fst X' Y' ≫ g₁', snd X' Y' ≫ g₂'] (M.pull b)) :=
    LBIso.chartPull
      (chartPullLinComb L a _ _ _ U.left fun I => key hA f₁ f₂ f₁' f₂' e₁ e₂ I.down)
      (chartPullLinComb M b _ _ _ U.left fun I => key hB g₁ g₂ g₁' g₂' e₃ e₄ I.down) H
  have hLa : (L.pull a).IsLB := DVR.linComb_isLB _ hL _ _
  have hMb : (M.pull b).IsLB := DVR.linComb_isLB _ hM _ _
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hM' _ _)
    (PowPrimitive.lbIso_linComb iL.symm _ _)
    (LBIso.trans (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hMb _ _) (DVR.linComb_isLB _ hM' _ _) H₁
      (PowPrimitive.lbIso_linComb iM _ _))

end GlobalTheory.CM

end
