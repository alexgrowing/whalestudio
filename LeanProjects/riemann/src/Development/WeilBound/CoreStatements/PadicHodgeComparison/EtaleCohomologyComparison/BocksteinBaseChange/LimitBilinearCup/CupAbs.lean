import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct CategoryTheory

namespace CrystallineSemistableComparison.CupAbs

universe w₁ w₂ w₃ u₁ u₂ u₃

section BC

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {M : Type u₁} {N : Type u₂} {P : Type u₃} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def bc (f : M →ₗ[R] N →ₗ[R] P) : A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] A ⊗[R] P :=
  TensorProduct.AlgebraTensorModule.curry
    ((LinearMap.baseChange A (TensorProduct.lift f)).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap)

theorem bc_tmul (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    bc A f ((1 : A) ⊗ₜ[R] m) ((1 : A) ⊗ₜ[R] n) = (1 : A) ⊗ₜ[R] f m n := by
  simp [bc]

end BC

section Lim

variable {R : Type} [CommRing R] {S₁ : Sys.{w₁} R} {S₂ : Sys.{w₂} R} {S₃ : Sys.{w₃} R}

def limBil (b : ∀ m, S₁.M m →ₗ[R] S₂.M m →ₗ[R] S₃.M m)
    (hb : ∀ m x y, S₃.r m (b (m + 1) x y) = b m (S₁.r m x) (S₂.r m y)) : S₁.lim →ₗ[R] S₂.lim →ₗ[R] S₃.lim :=
  LinearMap.mk₂ R (fun x y => ⟨fun m => b m (x.1 m) (y.1 m), fun m => by rw [hb, x.2 m, y.2 m]⟩)
    (fun x x' y => Subtype.ext (funext fun m => by simp))
    (fun c x y => Subtype.ext (funext fun m => by simp))
    (fun x y y' => Subtype.ext (funext fun m => by simp))
    (fun c x y => Subtype.ext (funext fun m => by simp))

theorem limBil_apply (b : ∀ m, S₁.M m →ₗ[R] S₂.M m →ₗ[R] S₃.M m)
    (hb : ∀ m x y, S₃.r m (b (m + 1) x y) = b m (S₁.r m x) (S₂.r m y)) (x : S₁.lim) (y : S₂.lim) (m : ℕ) :
    (limBil b hb x y).1 m = b m (x.1 m) (y.1 m) := rfl

end Lim

section One

theorem mapH_cls' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w₁} R} {L : Cx.{w₂} R'}
    (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (b : L.X n) (hb : L.d n b = 0) (e : φ.f n a = b) :
    φ.mapH n (K.cls a ha) = L.cls b hb := by
  subst e
  exact CrystallineSemistableComparison.P.mapH_cls φ n a ha hb

theorem pull_one {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u₁} [Category.{u₂} C]
    {C' : Type u₃} [Category.{w₃} C'] {A : C ⥤ CommAlgCat.{w₁} R} {A' : C' ⥤ CommAlgCat.{w₂} R'}
    (m : CH.Mor (CH.modF A) (CH.modF A') σ) (h1 : ∀ T, m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' :=
  mapH_cls' m.hom 0 _ _ _ _ (funext fun _ => h1 _)

end One

end CrystallineSemistableComparison.CupAbs
