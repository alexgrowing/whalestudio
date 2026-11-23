import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Proj

variable {A : Type*} [CommRing A] {n : ℕ}

theorem entIn_transpose {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (h : EntIn J X) : EntIn J X.transpose :=
  fun i j => h j i

theorem entIn_smul {J : AddSubgroup A} (e : A) (hJ : ∀ x ∈ J, e * x ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (h : EntIn J X) : EntIn J (e • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact hJ _ (h i j)

theorem proj_inv (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (e : A) (he : e * e = e) (x : GL (Fin n) A)
    (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J (e • ((x : Matrix (Fin n) (Fin n) A) - 1))) :
    EntIn J (e • (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1)) := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXd
  set Y := ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 with hYd
  have hx1 : (x : Matrix (Fin n) (Fin n) A) = 1 + X := by rw [hXd]; abel
  have hy1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 + Y := by rw [hYd]; abel
  have hXY : X + Y + X * Y = 0 := by
    have h1 : (x : Matrix (Fin n) (Fin n) A) * ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + X) * (1 + Y) = (1 : Matrix (Fin n) (Fin n) A) + (X + Y + X * Y) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hYX : Y + X + Y * X = 0 := by
    have h1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (x : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + Y) * (1 + X) = (1 : Matrix (Fin n) (Fin n) A) + (Y + X + Y * X) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hv : (1 + e • X) * (1 + e • Y) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • Y + (e • X + e • (X * Y)) = e • (X + Y + X * Y) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hXY, smul_zero, add_zero]
  have hv' : (1 + e • Y) * (1 + e • X) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • X + (e • Y + e • (Y * X)) = e • (Y + X + Y * X) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hYX, smul_zero, add_zero]
  let y : GL (Fin n) A := ⟨1 + e • X, 1 + e • Y, hv, hv'⟩
  have hyv : (y : Matrix (Fin n) (Fin n) A) - 1 = e • X := by simp [y]
  have hyi : ((y⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 = e • Y := by
    show (1 + e • Y) - 1 = e • Y
    simp
  have key := inv_sub_one f hf hJ y (fun i j h => by
      rw [hyv, Matrix.smul_apply, hlow i j h, smul_zero]) (by rw [hyv]; exact hx)
  rw [hyi] at key
  exact key.1

end Proj

section Close

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L c') :
    x ∈ latS L c := by
  rw [h] at hx; exact latS_mono ht hx

theorem entIn_latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L c') X) : EntIn (latS L c) X := fun i j => latS_of_eq h ht (hX i j)

end Close

end Formalism.L2.SG.Pf.ProdEApprox
