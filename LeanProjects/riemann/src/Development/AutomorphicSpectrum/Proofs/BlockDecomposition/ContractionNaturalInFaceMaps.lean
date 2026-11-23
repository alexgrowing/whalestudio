import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfC.ConPr

theorem Con_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (q : ℕ) (B : Bi F p q) (b : Fin (q + 1) ⥤ C) :
    Con F Ξ q B b = con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) (F.obj (b.obj (Fin.last q))) Ξ
      (fun a ↦ B a b) := rfl

theorem con_lTensor {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (Ξ : (∀ i, V i) →ₗ[R] R) (φ : M →ₗ[R] M') (u : ∀ i, V i ⊗[R] M) :
    con V M' Ξ (fun i ↦ LinearMap.lTensor (V i) φ (u i)) = φ (con V M Ξ u) := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((0 : ∀ i, V i ⊗[R] M) i)) = 0 := by
      funext i; simp
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.lTensor_tmul]
    rw [con_pure, con_pure, map_smul]
  | ha u v hu hv =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((u + v) i)) =
        (fun i ↦ LinearMap.lTensor (V i) φ (u i)) + (fun i ↦ LinearMap.lTensor (V i) φ (v i)) := by
      funext i; simp
    rw [h, map_add, map_add, map_add, hu, hv]

theorem tmap_id_eq {R : Type} [CommRing R] {A B B' : Type} [CommRing A] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R B'] (g : B →ₐ[R] B') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id R A) g t = LinearMap.lTensor A g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Con_prB {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q q' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (B : Bi F p q) :
    Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B) := by
  funext b
  rw [pr_apply, Con_apply, Con_apply]
  simp only [prB_apply, tmap_id_eq]
  exact con_lTensor (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) Ξ _ _

theorem con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (M : Type) [AddCommGroup M] [Module R M]
    (u : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) :
    con (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ'
      (fun a ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        (u (e.monotone.functor ⋙ a))) =
    con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) M (Ξ' ∘ₗ (pr F e).toLinearMap) u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun a : Fin (p' + 1) ⥤ C ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        ((0 : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) (e.monotone.functor ⋙ a))) = 0 := by
      funext a; exact map_zero _
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.rTensor_tmul]
    rw [con_pure (V := fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))]
    exact con_pure (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ' (pr F e f) m
  | ha u v hu hv =>
    rw [map_add, ← hu, ← hv, ← map_add]
    congr 1
    funext a
    exact map_add _ _ _

theorem tmap_id_eq' {R : Type} [CommRing R] {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B] (g : A →ₐ[R] A') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map g (AlgHom.id R B) t = LinearMap.rTensor B g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (B : Bi F p q) :
    Con F Ξ' q (prA F e B) = Con F (Ξ' ∘ₗ (pr F e).toLinearMap) q B := by
  funext b
  rw [Con_apply, Con_apply]
  simp only [prA_apply, tmap_id_eq']
  exact con_prA F Ξ' e _ (fun a ↦ B a b)

theorem con_pr : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) :=
  fun F _ _ _ _ _ _ Ξ Ξ' e e' ↦ ⟨Con_prB F Ξ e, Con_prA F Ξ' e'⟩

end GlobalTheory.CompanionTheory.HopfC.ConPr
