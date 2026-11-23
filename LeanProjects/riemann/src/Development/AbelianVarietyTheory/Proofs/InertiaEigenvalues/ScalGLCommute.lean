import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

def scalGL (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] : Rˣ →* GL n R :=
  Units.map (Matrix.scalar n : R →+* Matrix n n R).toMonoidHom

theorem scalGL_val (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) :
    ((scalGL n u : GL n R) : Matrix n n R) = Matrix.scalar n (u : R) := rfl

theorem scalGL_commute (n : Type) [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) (M : GL n R) :
    Commute (scalGL n u) M :=
  Units.ext ((Matrix.scalar_commute (u : R) (fun _ => mul_comm _ _) (M : Matrix n n R)))

theorem scalGL_mul_val {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (u : Rˣ) (M : GL n R) :
    ((scalGL n u * M : GL n R) : Matrix n n R) = (u : R) • (M : Matrix n n R) := by
  rw [Units.val_mul, scalGL_val, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

def twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ)
    (a : ℤ) : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) where
  toFun g := scalGL n (χ g ^ a) * (ρ.comp (Subgroup.inclusion (GK_le hK))) g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_zpow]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, (scalGL_commute n _ _).eq]

theorem twist_val {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ)
    (a : ℤ) (g : ↥(GK K')) : (twist hK ρ χ a g : Matrix n n ↥(MaximalUnramifiedExtension l)) =
      (((χ g ^ a : (↥(MaximalUnramifiedExtension l))ˣ)) : ↥(MaximalUnramifiedExtension l)) • (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) :=
  scalGL_mul_val _ _

end GlobalTheory.PMon.Twist

end
