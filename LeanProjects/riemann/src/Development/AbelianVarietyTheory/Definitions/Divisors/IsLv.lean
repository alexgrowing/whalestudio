import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SphericalEisensteinConvergence
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ}

structure Fr (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  herm₀ : IsHermND σ J₀
  cc : cT (σ : E →+* E) C * J * C = 0
  dd : cT (σ : E →+* E) D * J * D = 0
  cd : cT (σ : E →+* E) C * J * D = 1
  dc : cT (σ : E →+* E) D * J * C = 1
  cz : cT (σ : E →+* E) C * J * Z = 0
  dz : cT (σ : E →+* E) D * J * Z = 0
  zc : cT (σ : E →+* E) Z * J * C = 0
  zd : cT (σ : E →+* E) Z * J * D = 0
  zz : cT (σ : E →+* E) Z * J * Z = J₀
  sum : C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J) = 1
  dim : m + 2 * j = n

def fixG {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) where
  carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change _ * _ = _ at ha hb ⊢
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, ha]
  inv_mem' := fun {a} ha => by
    change _ * _ = _ at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

structure IsLv (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J) : Prop where
  cont : Continuous lv
  onC : ∀ α, (matHom _ σ J (lv α)).1 * adMat F C = adMat F C * α.1
  onD : ∀ α, (matHom _ σ J (lv α)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1
  onZ : ∀ α, (matHom _ σ J (lv α)).1 * adMat F Z = adMat F Z
  rat : ∀ δ : GL (Fin j) E, lv (bc (inclR (F := F) (AF F)) δ) ∈ ratPts σ J

def plus (J₀ : Matrix (Fin m) (Fin m) E) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) : Matrix (Fin m) (Fin j) (AF F ⊗[F] E) :=
  adMat F J₀⁻¹ * cT (sigR (AF F) σ) b

structure Crd (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) (u : GAd σ J)
    (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) : Prop where
  onC : (matHom _ σ J u).1 * adMat F C = adMat F C
  onZ : (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b
  onD : (matHom _ σ J u).1 * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c

variable (F E) in

abbrev tor (l : Fin j → ℤ) : GL (Fin j) (AF F ⊗[F] E) := GlobalTheory.Eis.Conv.dg (GlobalTheory.Eis.Conv.halfE F E) l

variable (F) in

abbrev bse : ℝ := 4 ^ Fintype.card (InfinitePlace F)

example (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) :
    Crd σ J C D Z J₀ 1 0 0 := ⟨by simp, by simp, by simp [plus, cT]⟩

example (h : IsCMExt F E σ) : Fr σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) !![0; 1]
    (0 : Matrix (Fin 2) (Fin 0) E) 1 := by
  refine ⟨h, ⟨fun i j => ?_, by simp⟩, ⟨fun i => i.elim0, by simp⟩, ?_, ?_, ?_, ?_, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_, rfl⟩
  · fin_cases i <;> fin_cases j <;> simp
  all_goals ext i j; fin_cases i <;> fin_cases j <;> simp [cT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end GlobalTheory.SphEis

end
