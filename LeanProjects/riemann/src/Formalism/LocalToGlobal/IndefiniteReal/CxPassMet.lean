import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.BranchSandwichDivisors.StatementL

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass.BlockMetrics

open Formalism.L2.DIV

theorem inv_smul_ne {n : ℕ} (k : ℂ) (hk : k ≠ 0) (A : Matrix (Fin n) (Fin n) ℂ) :
    (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk, one_smul, Matrix.nonsing_inv_mul _ h]
  · have h' : ¬ IsUnit (k • A).det := by
      rw [Matrix.det_smul]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', smul_zero]

theorem quotMetC_smul {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (P : Matrix (Fin d) (Fin n) ℂ)
    (c : ℝ) (hc : 0 < c) : quotMetC P ((c : ℂ) • A) = (c : ℂ) • quotMetC P A := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold quotMetC
  rw [inv_smul_ne _ hc', Matrix.mul_smul, Matrix.smul_mul, inv_smul_ne _ (inv_ne_zero hc'), inv_inv]

theorem unitary_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : Rᴴ * A * R = A) (hRu : IsUnit R.det) :
    R * A⁻¹ * Rᴴ = A⁻¹ := by
  have h1 : Rᴴ * A = A * R⁻¹ := by
    calc Rᴴ * A = Rᴴ * A * R * R⁻¹ := by
          rw [Matrix.mul_assoc (Rᴴ * A), Matrix.mul_nonsing_inv _ hRu, Matrix.mul_one]
      _ = A * R⁻¹ := by rw [hR]
  symm
  apply Matrix.inv_eq_left_inv
  calc R * A⁻¹ * Rᴴ * A = R * A⁻¹ * (Rᴴ * A) := by rw [Matrix.mul_assoc]
    _ = R * (A⁻¹ * A) * R⁻¹ := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, Matrix.mul_nonsing_inv _ hRu]

theorem quotMetC_unitary {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (P : Matrix (Fin d) (Fin n) ℂ) (hP : Function.Surjective P.mulVec)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : Rᴴ * A * R = A) (hRu : IsUnit R.det)
    (N : Matrix (Fin d) (Fin d) ℂ) (hN : P * R = N * P) :
    Nᴴ * quotMetC P A * N = quotMetC P A := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hU : R * A⁻¹ * Rᴴ = A⁻¹ := unitary_inv A hAu R hR hRu
  unfold quotMetC
  set Q := P * A⁻¹ * Pᴴ with hQdef
  have hNQ : N * Q * Nᴴ = Q := by
    have e : N * Q * Nᴴ = (N * P) * A⁻¹ * (N * P)ᴴ := by
      rw [hQdef, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, ← hN, Matrix.conjTranspose_mul]
    calc P * R * A⁻¹ * (Rᴴ * Pᴴ) = P * (R * A⁻¹ * Rᴴ) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hU]
  by_cases hq : IsUnit Q.det
  · have h1 : N.det * Q.det * (Nᴴ).det = Q.det := by rw [← Matrix.det_mul, ← Matrix.det_mul, hNQ]
    have h2 : IsUnit (N.det * Q.det * (Nᴴ).det) := by rw [h1]; exact hq
    have hNdet : IsUnit N.det := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2)
    have hNh : IsUnit (Nᴴ).det := by rw [Matrix.det_conjTranspose]; exact hNdet.star
    have hinv : Q⁻¹ = (Nᴴ)⁻¹ * (Q⁻¹ * N⁻¹) := by
      conv_lhs => rw [← hNQ]
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc Nᴴ * Q⁻¹ * N = Nᴴ * ((Nᴴ)⁻¹ * (Q⁻¹ * N⁻¹)) * N := by rw [← hinv]
      _ = (Nᴴ * (Nᴴ)⁻¹) * Q⁻¹ * (N⁻¹ * N) := by simp only [Matrix.mul_assoc]
      _ = Q⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hNh, Matrix.nonsing_inv_mul _ hNdet, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hq]
    simp

private theorem eq_of_mul_eq_mul_right_of_mulVec_surjective {a b c : ℕ} (X Y : Matrix (Fin a) (Fin b) ℂ) (P : Matrix (Fin b) (Fin c) ℂ)
    (hP : Function.Surjective P.mulVec) (h : X * P = Y * P) : X = Y := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨u, rfl⟩ := hP v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private theorem eq_of_mul_eq_mul_left_of_mulVec_injective {a b c : ℕ} (J : Matrix (Fin a) (Fin b) ℂ) (X Y : Matrix (Fin b) (Fin c) ℂ)
    (hJ : Function.Injective J.mulVec) (h : J * X = J * Y) : X = Y := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  apply hJ
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem quotMetC_through {n m d d' : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (P : Matrix (Fin d) (Fin n) ℂ) (hP : Function.Surjective P.mulVec)
    (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin m) (Fin n) ℂ) (hDC : D * C = 1)
    (hE : (C * D)ᴴ * A = A * (C * D))
    (N : Matrix (Fin d) (Fin d) ℂ) (hN : P * (C * D) = N * P)
    (P' : Matrix (Fin d') (Fin m) ℂ) (hP' : Function.Surjective P'.mulVec)
    (J : Matrix (Fin d) (Fin d') ℂ) (hJ : Function.Injective J.mulVec)
    (hPC : P * C = J * P') :
    quotMetC P' (Cᴴ * A * C) = Jᴴ * quotMetC P A * J := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hpd : (quotMetC P A).PosDef := (quotRestrPosDef n d A hA).1 P hP
  have hQu : IsUnit (P * A⁻¹ * Pᴴ).det := by
    have h1 := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
    unfold quotMetC at h1
    exact Matrix.isUnit_nonsing_inv_det_iff.mp h1
  have hCE : Cᴴ * (C * D)ᴴ = Cᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hDC,
      Matrix.conjTranspose_one, Matrix.one_mul]
  have hCD : Cᴴ * Dᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hDC, Matrix.conjTranspose_one]
  have hA' : (Cᴴ * A * C)⁻¹ = D * A⁻¹ * Dᴴ := by
    apply Matrix.inv_eq_right_inv
    calc Cᴴ * A * C * (D * A⁻¹ * Dᴴ) = Cᴴ * (A * (C * D)) * A⁻¹ * Dᴴ := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((C * D)ᴴ * A) * A⁻¹ * Dᴴ := by rw [hE]
      _ = (Cᴴ * (C * D)ᴴ) * (A * A⁻¹) * Dᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCE, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one, hCD]
  have hEA : A⁻¹ * (C * D)ᴴ = (C * D) * A⁻¹ := by
    calc A⁻¹ * (C * D)ᴴ = A⁻¹ * (C * D)ᴴ * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one]
      _ = A⁻¹ * ((C * D)ᴴ * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * (C * D)) * A⁻¹ := by rw [hE]
      _ = (A⁻¹ * A) * (C * D) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (C * D) * A⁻¹ := by rw [Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul]
  have hJP : J * P' * D = N * P := by rw [← hPC, Matrix.mul_assoc, hN]
  have hNJ : N * J = J := by
    apply eq_of_mul_eq_mul_right_of_mulVec_surjective _ _ P' hP'
    calc N * J * P' = N * (P * C) := by rw [Matrix.mul_assoc, hPC]
      _ = P * (C * D) * C := by rw [← Matrix.mul_assoc, ← hN]
      _ = P * C := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hDC, Matrix.mul_one]
      _ = J * P' := hPC
  have hNQ : P * A⁻¹ * Pᴴ * Nᴴ = N * (P * A⁻¹ * Pᴴ) := by
    calc P * A⁻¹ * Pᴴ * Nᴴ = P * A⁻¹ * (N * P)ᴴ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = P * (A⁻¹ * (C * D)ᴴ) * Pᴴ := by rw [← hN, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = P * (C * D) * A⁻¹ * Pᴴ := by rw [hEA]; simp only [Matrix.mul_assoc]
      _ = N * (P * A⁻¹ * Pᴴ) := by rw [hN]; simp only [Matrix.mul_assoc]
  have hJQ : J * (P' * (D * A⁻¹ * Dᴴ) * P'ᴴ) * Jᴴ = N * (P * A⁻¹ * Pᴴ) * Nᴴ := by
    calc J * (P' * (D * A⁻¹ * Dᴴ) * P'ᴴ) * Jᴴ = (J * P' * D) * A⁻¹ * (J * P' * D)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = N * (P * A⁻¹ * Pᴴ) * Nᴴ := by
          rw [hJP, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hkey : P' * (D * A⁻¹ * Dᴴ) * P'ᴴ * (Jᴴ * (P * A⁻¹ * Pᴴ)⁻¹ * J) = 1 := by
    apply eq_of_mul_eq_mul_left_of_mulVec_injective J _ _ hJ
    calc J * (P' * (D * A⁻¹ * Dᴴ) * P'ᴴ * (Jᴴ * (P * A⁻¹ * Pᴴ)⁻¹ * J))
          = (J * (P' * (D * A⁻¹ * Dᴴ) * P'ᴴ) * Jᴴ) * (P * A⁻¹ * Pᴴ)⁻¹ * J := by simp only [Matrix.mul_assoc]
      _ = N * (P * A⁻¹ * Pᴴ * Nᴴ) * (P * A⁻¹ * Pᴴ)⁻¹ * J := by rw [hJQ]; simp only [Matrix.mul_assoc]
      _ = N * N * ((P * A⁻¹ * Pᴴ) * (P * A⁻¹ * Pᴴ)⁻¹) * J := by rw [hNQ]; simp only [Matrix.mul_assoc]
      _ = J * (1 : Matrix (Fin d') (Fin d') ℂ) := by
          rw [Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, hNJ, hNJ]
  unfold quotMetC
  rw [hA']
  exact Matrix.inv_eq_right_inv hkey

theorem metOf_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 < c) :
    metOf ((c : ℂ) • Y) = (((c ^ 2)⁻¹ : ℝ) : ℂ) • metOf Y := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold metOf
  rw [inv_smul_ne _ hc', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  push_cast
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  ring

theorem majAt_scaleFrame {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 < c) (v : InfinitePlace K) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (Formalism.BranchingDeterminantCap.scaleFrame c X) v x y =
      (((c ^ 2)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y := by
  rw [Formalism.L2.DIV.majAt_eq, Formalism.L2.DIV.majAt_eq]
  simp only [Formalism.BranchingDeterminantCap.scaleFrame]
  rw [metOf_smul _ c hc, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end Formalism.IndefR.CxPass.BlockMetrics

namespace Formalism.IndefR.CxPass.BlockMetrics

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

def QuotThrough : Prop := ∀ (n m d d' : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    ∀ (P : Matrix (Fin d) (Fin n) ℂ), Function.Surjective P.mulVec →
    ∀ (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin m) (Fin n) ℂ), D * C = 1 → (C * D)ᴴ * A = A * (C * D) →
    ∀ (N : Matrix (Fin d) (Fin d) ℂ), P * (C * D) = N * P →
    ∀ (P' : Matrix (Fin d') (Fin m) ℂ), Function.Surjective P'.mulVec →
    ∀ (J : Matrix (Fin d) (Fin d') ℂ), Function.Injective J.mulVec → P * C = J * P' →
    quotMetC P' (Cᴴ * A * C) = Jᴴ * quotMetC P A * J

def QuotUnitary : Prop := ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    ∀ (P : Matrix (Fin d) (Fin n) ℂ), Function.Surjective P.mulVec →
    ∀ (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ * A * R = A → IsUnit R.det →
    ∀ (N : Matrix (Fin d) (Fin d) ℂ), P * R = N * P → Nᴴ * quotMetC P A * N = quotMetC P A

section Gen

variable {α : Type} [CommRing α] [StarRing α]

theorem blk_adj {a b : ℕ} (V : Matrix (Fin a) (Fin b) α) (T T' : Matrix (Fin b) (Fin b) α)
    (F F' H : Matrix (Fin a) (Fin a) α) (hT : V * T = F * V) (hT' : V * T' = F' * V)
    (hF : F'ᴴ * H = H * F) : T'ᴴ * (Vᴴ * H * V) = (Vᴴ * H * V) * T := by
  have e : T'ᴴ * Vᴴ = Vᴴ * F'ᴴ := by
    rw [← Matrix.conjTranspose_mul, hT', Matrix.conjTranspose_mul]
  calc T'ᴴ * (Vᴴ * H * V) = (T'ᴴ * Vᴴ) * H * V := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (F'ᴴ * H) * V := by rw [e]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * (F * V) := by rw [hF]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * V * T := by rw [← hT]; simp only [Matrix.mul_assoc]

theorem blk_unit {a b : ℕ} (V : Matrix (Fin a) (Fin b) α) (T : Matrix (Fin b) (Fin b) α)
    (F H : Matrix (Fin a) (Fin a) α) (hT : V * T = F * V) (hF : Fᴴ * H * F = H) :
    Tᴴ * (Vᴴ * H * V) * T = Vᴴ * H * V := by
  have e : Tᴴ * Vᴴ = Vᴴ * Fᴴ := by
    rw [← Matrix.conjTranspose_mul, hT, Matrix.conjTranspose_mul]
  calc Tᴴ * (Vᴴ * H * V) * T = (Tᴴ * Vᴴ) * H * (V * T) := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (Fᴴ * H * F) * V := by rw [e, hT]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * V := by rw [hF]

theorem blk_pull {a b c : ℕ} (V : Matrix (Fin a) (Fin b) α) (W : Matrix (Fin a) (Fin c) α)
    (C : Matrix (Fin b) (Fin c) α) (H : Matrix (Fin a) (Fin a) α) (hC : V * C = W) :
    Wᴴ * H * W = Cᴴ * (Vᴴ * H * V) * C := by
  rw [← hC, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blk_ext {a b : ℕ} {A A' : Matrix (Fin a) (Fin b) α} (h : ∀ x, A *ᵥ x = A' *ᵥ x) : A = A' := by
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h x])

end Gen

theorem blk_orth {K : Type} [Field K] [StarRing K] {n m d d' : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (z : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hPr : Pr = orthPr H z)
    (H' : Matrix (Fin m) (Fin m) K) (z' : Matrix (Fin m) (Fin d') K) (P' : Matrix (Fin d') (Fin m) K)
    (hP' : IsOrthProj H' z' P') (R : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin d) (Fin d') K)
    (hR : zᴴ * H * R = Q * (z'ᴴ * H')) : Pr * R = (Pr * R * z') * P' := by
  obtain ⟨-, h2⟩ := hP'
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  have hR' : zᴴ * H * R = Q * z'ᴴ * H' := by rw [hR]; simp only [Matrix.mul_assoc]
  have e : Q * z'ᴴ * H' * z' * P' = Q * z'ᴴ * H' := by
    calc Q * z'ᴴ * H' * z' * P' = Q * (z'ᴴ * H' * (z' * P')) := by simp only [Matrix.mul_assoc]
      _ = Q * (z'ᴴ * H') := by rw [← h2]
      _ = Q * z'ᴴ * H' := by simp only [Matrix.mul_assoc]
  subst hPr
  unfold orthPr
  calc (zᴴ * H * z)⁻¹ * (zᴴ * H) * R = (zᴴ * H * z)⁻¹ * (zᴴ * H * R) := by simp only [Matrix.mul_assoc]
    _ = (zᴴ * H * z)⁻¹ * (Q * z'ᴴ * H' * z' * P') := by rw [hR', e]
    _ = (zᴴ * H * z)⁻¹ * (zᴴ * H) * R * z' * P' := by rw [← hR']; simp only [Matrix.mul_assoc]

theorem blk_maj {K : Type} [Field K] [NumberField K] {n d : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (J : Matrix (Fin d) (Fin n) K) (c : ℂ)
    (hm : metOf (X v) = c • ((J.map v.embedding)ᴴ * metOf (Y v) * J.map v.embedding)) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      c * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Y v (J *ᵥ x) (J *ᵥ y) := by
  rw [Formalism.L2.DIV.majAt_eq, Formalism.L2.DIV.majAt_eq, hm]
  have hJ : ∀ z : Fin n → K, (fun i => v.embedding ((J *ᵥ z) i)) =
      (J.map v.embedding) *ᵥ (fun i => v.embedding (z i)) := by
    intro z; ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hJ x, hJ y, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

section Abs

variable {K : Type} [Field K] [StarRing K]

private theorem orthPr_mul_eq_mul_orthPr_of_adjoint {N dg : ℕ} (Hg : Matrix (Fin N) (Fin N) K) (zg : Matrix (Fin N) (Fin dg) K)
    (Pg : Matrix (Fin dg) (Fin N) K) (hPg : Pg = orthPr Hg zg) (hPgO : IsOrthProj Hg zg Pg)
    (RK RK' : Matrix (Fin N) (Fin N) K) (hadj : RK'ᴴ * Hg = Hg * RK) (W : Matrix (Fin dg) (Fin dg) K)
    (hW : RK' * zg = zg * W) (ρ : Matrix (Fin dg) (Fin dg) K) (hzρ : zg * ρ = RK * zg) :
    Pg * RK = ρ * Pg := by
  obtain ⟨h1, h2⟩ := hPgO
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  have key : Pg * RK = ((zgᴴ * Hg * zg)⁻¹ * Wᴴ) * (zgᴴ * Hg) := by
    have e1 : zgᴴ * RK'ᴴ = Wᴴ * zgᴴ := by
      rw [← Matrix.conjTranspose_mul, hW, Matrix.conjTranspose_mul]
    rw [hPg]
    unfold orthPr
    calc (zgᴴ * Hg * zg)⁻¹ * (zgᴴ * Hg) * RK = (zgᴴ * Hg * zg)⁻¹ * (zgᴴ * (Hg * RK)) := by
          simp only [Matrix.mul_assoc]
      _ = (zgᴴ * Hg * zg)⁻¹ * ((zgᴴ * RK'ᴴ) * Hg) := by rw [← hadj]; simp only [Matrix.mul_assoc]
      _ = ((zgᴴ * Hg * zg)⁻¹ * Wᴴ) * (zgᴴ * Hg) := by rw [e1]; simp only [Matrix.mul_assoc]
  have e2 : Pg * RK = Pg * RK * zg * Pg := by
    rw [key]
    calc (zgᴴ * Hg * zg)⁻¹ * Wᴴ * (zgᴴ * Hg) = (zgᴴ * Hg * zg)⁻¹ * Wᴴ * (zgᴴ * Hg * (zg * Pg)) := by
          rw [← h2]
      _ = (zgᴴ * Hg * zg)⁻¹ * Wᴴ * (zgᴴ * Hg) * zg * Pg := by simp only [Matrix.mul_assoc]
  calc Pg * RK = Pg * RK * zg * Pg := e2
    _ = Pg * (RK * zg) * Pg := by simp only [Matrix.mul_assoc]
    _ = Pg * zg * ρ * Pg := by rw [← hzρ]; simp only [Matrix.mul_assoc]
    _ = ρ * Pg := by rw [h1, Matrix.one_mul]

theorem blk_transAbs {N M dg db : ℕ} (Hg : Matrix (Fin N) (Fin N) K) (Hb : Matrix (Fin M) (Fin M) K)
    (zg : Matrix (Fin N) (Fin dg) K) (zb : Matrix (Fin M) (Fin db) K) (Pg : Matrix (Fin dg) (Fin N) K)
    (Pb : Matrix (Fin db) (Fin M) K) (hPg : Pg = orthPr Hg zg) (hPgO : IsOrthProj Hg zg Pg)
    (hPbO : IsOrthProj Hb zb Pb) (CK : Matrix (Fin N) (Fin M) K) (DK : Matrix (Fin M) (Fin N) K)
    (hDC : DK * CK = 1) (hEadj : (CK * DK)ᴴ * Hg = Hg * (CK * DK)) (c : K) (hHb : c • Hb = CKᴴ * Hg * CK)
    (W : Matrix (Fin dg) (Fin dg) K) (hW : CK * DK * zg = zg * W) (V : Matrix (Fin db) (Fin dg) K)
    (hV : DK * zg = zb * V) (J : Matrix (Fin dg) (Fin db) K) (hzJ : zg * J = CK * zb) :
    Pg * (CK * DK) = (Pg * (CK * DK) * zg) * Pg ∧ Pg * CK = J * Pb := by
  have hP1 : Pg * (CK * DK) = W * Pg :=
    orthPr_mul_eq_mul_orthPr_of_adjoint Hg zg Pg hPg hPgO (CK * DK) (CK * DK) hEadj W hW W hW.symm
  refine ⟨?_, ?_⟩
  · rw [hP1, Matrix.mul_assoc W Pg zg, hPgO.1, Matrix.mul_one]
  · obtain ⟨hb1, hb2⟩ := hPbO
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hb2
    have hHC : Hg * CK = c • (DKᴴ * Hb) := by
      have h3 : DKᴴ * CKᴴ * Hg * CK = Hg * CK := by
        calc DKᴴ * CKᴴ * Hg * CK = (CK * DK)ᴴ * Hg * CK := by rw [Matrix.conjTranspose_mul]
          _ = Hg * (CK * DK) * CK := by rw [hEadj]
          _ = Hg * CK := by rw [Matrix.mul_assoc Hg, Matrix.mul_assoc CK, hDC, Matrix.mul_one]
      rw [← h3, ← Matrix.mul_smul, hHb]
      simp only [Matrix.mul_assoc]
    have e3 : zgᴴ * Hg * CK = c • (Vᴴ * (zbᴴ * Hb)) := by
      conv_lhs => rw [Matrix.mul_assoc, hHC, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
        hV, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have key : Pg * CK = (c • ((zgᴴ * Hg * zg)⁻¹ * Vᴴ)) * (zbᴴ * Hb) := by
      rw [hPg]
      unfold orthPr
      calc (zgᴴ * Hg * zg)⁻¹ * (zgᴴ * Hg) * CK = (zgᴴ * Hg * zg)⁻¹ * (zgᴴ * Hg * CK) :=
            Matrix.mul_assoc _ _ _
        _ = (c • ((zgᴴ * Hg * zg)⁻¹ * Vᴴ)) * (zbᴴ * Hb) := by
            rw [e3, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc ((zgᴴ * Hg * zg)⁻¹) Vᴴ]
    have hz : Pg * CK * zb = J := by
      rw [Matrix.mul_assoc, ← hzJ, ← Matrix.mul_assoc, hPgO.1, Matrix.one_mul]
    calc Pg * CK = (c • ((zgᴴ * Hg * zg)⁻¹ * Vᴴ)) * (zbᴴ * Hb) := key
      _ = (c • ((zgᴴ * Hg * zg)⁻¹ * Vᴴ)) * (zbᴴ * Hb * (zb * Pb)) := by rw [← hb2]
      _ = (c • ((zgᴴ * Hg * zg)⁻¹ * Vᴴ)) * (zbᴴ * Hb) * zb * Pb := by simp only [Matrix.mul_assoc]
      _ = Pg * CK * zb * Pb := by rw [← key]
      _ = J * Pb := by rw [hz]

theorem blk_invAbs {N dg : ℕ} (Hg : Matrix (Fin N) (Fin N) K) (zg : Matrix (Fin N) (Fin dg) K)
    (Pg : Matrix (Fin dg) (Fin N) K) (hPg : Pg = orthPr Hg zg) (hPgO : IsOrthProj Hg zg Pg)
    (RK RK' : Matrix (Fin N) (Fin N) K) (hadj : RK'ᴴ * Hg = Hg * RK) (W : Matrix (Fin dg) (Fin dg) K)
    (hW : RK' * zg = zg * W) (ρ : Matrix (Fin dg) (Fin dg) K) (hzρ : zg * ρ = RK * zg) :
    Pg * RK = ρ * Pg := by
  exact orthPr_mul_eq_mul_orthPr_of_adjoint Hg zg Pg hPg hPgO RK RK' hadj W hW ρ hzρ

theorem blk_smulH {a b c : ℕ} (H : Matrix (Fin a) (Fin a) K) (Vg : Matrix (Fin a) (Fin b) K)
    (Vb : Matrix (Fin a) (Fin c) K) (C : Matrix (Fin b) (Fin c) K) (Hg : Matrix (Fin b) (Fin b) K)
    (Hb : Matrix (Fin c) (Fin c) K) (k : K) (hk : k ≠ 0) (hHg : Hg = Vgᴴ * H * Vg)
    (hHb : Hb = k⁻¹ • (Vbᴴ * H * Vb)) (hC : Vg * C = Vb) : k • Hb = Cᴴ * Hg * C := by
  subst hHg hHb
  rw [smul_smul, mul_inv_cancel₀ hk, one_smul, ← hC, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blk_vR {a n : ℕ} (vg : Matrix (Fin a) (Fin n) K) (pr : Matrix (Fin n) (Fin a) K)
    (eg A : Matrix (Fin a) (Fin a) K) (h1 : vg * pr = eg) (h2 : eg * A = A * eg) (h3 : pr * vg = 1) :
    vg * (pr * A * vg) = A * vg := by
  calc vg * (pr * A * vg) = (vg * pr) * A * vg := by simp only [Matrix.mul_assoc]
    _ = A * (vg * (pr * vg)) := by rw [h1, h2, ← h1]; simp only [Matrix.mul_assoc]
    _ = A * vg := by rw [h3, Matrix.mul_one]

theorem blk_RR {a n : ℕ} (pr : Matrix (Fin n) (Fin a) K) (vg : Matrix (Fin a) (Fin n) K)
    (A A' : Matrix (Fin a) (Fin a) K) (hv' : vg * (pr * A' * vg) = A' * vg) (hAA : A * A' = 1)
    (h3 : pr * vg = 1) : (pr * A * vg) * (pr * A' * vg) = 1 := by
  calc (pr * A * vg) * (pr * A' * vg) = pr * A * (vg * (pr * A' * vg)) := by simp only [Matrix.mul_assoc]
    _ = pr * (A * A') * vg := by rw [hv']; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hAA, Matrix.mul_one, h3]

end Abs

section GlobalTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem blk_cm {a b : ℕ} (σ : K →+* ℂ) (E : Matrix (Fin a) (Fin b) K) (hE : ∀ i j, E i j ∈ cmMax K) :
    (Eᴴ).map σ = (E.map σ)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
  exact hE j i σ

theorem blk_cut (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    IsOrthProj B.S.H (B.vE ⟨X, P, ψ⟩) (B.vPr ⟨X, P, ψ⟩) ∧
      B.vE ⟨X, P, ψ⟩ * B.vPr ⟨X, P, ψ⟩ = B.S.gaMat B.r (goodAt X P ψ) := by
  have hg := good_at_spec K v0 hv0 G X hX P ψ
  exact orthogonal_projection_spec K v0 hv0 B.S (h.hpos v0) G B.r h.act _ hg.idem hg.selfAdj

theorem blk_vE_inj (B : BlockDat K G Pl0) (ℓ : Lvl K G) : Function.Injective (B.vE ℓ).mulVec :=
  (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).1

theorem blk_fix (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    B.S.gaMat B.r (goodAt X P ψ) * B.vE ⟨X, P, ψ⟩ = B.vE ⟨X, P, ψ⟩ := by
  obtain ⟨h1, h2⟩ := blk_cut B hv0 h X hX P ψ
  rw [← h2, Matrix.mul_assoc, h1.1, Matrix.mul_one]

theorem blk_HV (B : BlockDat K G Pl0) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) :
    B.HV ⟨X, P, ψ⟩ = (Nat.card P : K)⁻¹ • ((B.vE ⟨X, P, ψ⟩)ᴴ * B.S.H * B.vE ⟨X, P, ψ⟩) := rfl

theorem blk_HV_bot (B : BlockDat K G Pl0) (X : Finset (G → K)) :
    B.HV ⟨X, ⊥, 1⟩ = (B.vE ⟨X, ⊥, 1⟩)ᴴ * B.S.H * B.vE ⟨X, ⊥, 1⟩ := by
  rw [blk_HV]
  simp [Subgroup.card_bot]

theorem blk_goodBot (X : Finset (G → K)) : goodAt X (⊥ : Subgroup G) 1 = idemOf X := by
  unfold goodAt
  have hb : lvlIdem (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = 1 := by
    (simp [lvlIdem, MonoidAlgebra.one_def, Finset.univ_unique, Subgroup.card_bot]) <;> rfl
  rw [hb, mul_one]

theorem blk_gg (B : BlockDat K G Pl0) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    B.S.gaMat B.r (goodAt X ⊥ 1) * B.S.gaMat B.r (goodAt X P ψ) = B.S.gaMat B.r (goodAt X P ψ) := by
  rw [← (group_action_matrix_hom K B.S G B.r).2, blk_goodBot]
  unfold goodAt
  rw [← mul_assoc, (idempotent_central K G X hX).1]

theorem blk_comm (B : BlockDat K G Pl0) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (t : G) :
    B.S.gaMat B.r (goodAt X ⊥ 1) * B.S.actMat B.r t = B.S.actMat B.r t * B.S.gaMat B.r (goodAt X ⊥ 1) := by
  rw [← B.gaMat_single t, ← (group_action_matrix_hom K B.S G B.r).2, ← (group_action_matrix_hom K B.S G B.r).2, blk_goodBot,
    idemOf_central X hX]

theorem block_preserves_stable_subspace (B : BlockDat K G Pl0) (ℓ ℓ' : Lvl K G) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g)) (T : Matrix (Fin (B.nV ℓ')) (Fin (B.nV ℓ)) K) (a : MonoidAlgebra K G)
    (hT : B.vE ℓ' * T = B.S.gaMat B.r a * B.vE ℓ) {u : Fin (B.nV ℓ) → K} (hu : u ∈ B.Z0 ℓ Z) :
    T *ᵥ u ∈ B.Z0 ℓ' Z := by
  have hu' : B.S.basis.equivFun.symm (B.vE ℓ *ᵥ u) ∈ Z := (B.mem_goodPart_iff ℓ Z u).1 hu
  have e1 : B.vE ℓ *ᵥ u = B.S.basis.equivFun (B.S.basis.equivFun.symm (B.vE ℓ *ᵥ u)) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  show T *ᵥ u ∈ B.inV0 ℓ' Z
  rw [B.mem_goodPart_iff ℓ' Z, Matrix.mulVec_mulVec, hT, ← Matrix.mulVec_mulVec, e1, CSD.gaMat_mulVec_equivFun,
    LinearEquiv.symm_apply_apply]
  unfold CSD.gaOp
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  exact Z.sum_mem fun t _ => Z.smul_mem _ (hZ t hu')

theorem blk_range (B : BlockDat K G Pl0) (ℓ ℓ' : Lvl K G) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g)) (T : Matrix (Fin (B.nV ℓ')) (Fin (B.nV ℓ)) K) (a : MonoidAlgebra K G)
    (hT : B.vE ℓ' * T = B.S.gaMat B.r a * B.vE ℓ) : ∃ W, T * B.zE ℓ Z = B.zE ℓ' Z * W := by
  apply exists_mul_of_range_le
  rintro _ ⟨y, rfl⟩
  rw [show B.zE ℓ' Z = subE (B.Z0 ℓ' Z) from rfl, (subspace_image_spec K _ (B.Z0 ℓ' Z)).2,
    Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  exact block_preserves_stable_subspace B ℓ ℓ' Z hZ T a hT (B.zE_mem ℓ Z y)

end GlobalTheory

section BlkK

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem blk_adjE (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    (B.S.gaMat B.r (goodAt X P ψ))ᴴ * B.S.H = B.S.H * B.S.gaMat B.r (goodAt X P ψ) := by
  have := group_action_matrix_adjoint K B.S G B.r h.act (goodAt X P ψ)
  rwa [(good_at_spec K v0 hv0 G X hX P ψ).selfAdj] at this

theorem blk_transK (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (J *ᵥ x) = B.toF ⟨X, P, ψ⟩ Z x) :
    (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩) * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) = 1 ∧
    B.vE ⟨X, ⊥, 1⟩ * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) = B.vE ⟨X, P, ψ⟩ ∧
    B.vE ⟨X, ⊥, 1⟩ * ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩)) =
      B.S.gaMat B.r (goodAt X P ψ) * B.vE ⟨X, ⊥, 1⟩ ∧
    (∃ NK, B.Pq ⟨X, ⊥, 1⟩ Z * ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩)) =
      NK * B.Pq ⟨X, ⊥, 1⟩ Z) ∧
    B.Pq ⟨X, ⊥, 1⟩ Z * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) = J * B.Pq ⟨X, P, ψ⟩ Z ∧
    Function.Injective J.mulVec := by
  have hcb := blk_cut B hv0 h X hX P ψ
  have hcg := blk_cut B hv0 h X hX ⊥ 1
  have hfb := blk_fix B hv0 h X hX P ψ
  have hgg := blk_gg B X hX P ψ
  have hvC : B.vE ⟨X, ⊥, 1⟩ * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) = B.vE ⟨X, P, ψ⟩ := by
    calc B.vE ⟨X, ⊥, 1⟩ * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩)
        = B.S.gaMat B.r (goodAt X ⊥ 1) * B.vE ⟨X, P, ψ⟩ := by rw [← Matrix.mul_assoc, hcg.2]
      _ = B.S.gaMat B.r (goodAt X ⊥ 1) * (B.S.gaMat B.r (goodAt X P ψ) * B.vE ⟨X, P, ψ⟩) := by rw [hfb]
      _ = B.vE ⟨X, P, ψ⟩ := by rw [← Matrix.mul_assoc, hgg, hfb]
  have hDC : (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩) * (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) = 1 := by
    rw [Matrix.mul_assoc, hvC, hcb.1.1]
  have hvD : B.vE ⟨X, P, ψ⟩ * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩) =
      B.S.gaMat B.r (goodAt X P ψ) * B.vE ⟨X, ⊥, 1⟩ := by
    rw [← Matrix.mul_assoc, hcb.2]
  have hvE : B.vE ⟨X, ⊥, 1⟩ * ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩)) =
      B.S.gaMat B.r (goodAt X P ψ) * B.vE ⟨X, ⊥, 1⟩ := by
    rw [← Matrix.mul_assoc, hvC, hvD]
  have hHg := blk_HV_bot B X
  have hadj := blk_adjE B hv0 h X hX P ψ
  have hEadj : ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩))ᴴ * B.HV ⟨X, ⊥, 1⟩ =
      B.HV ⟨X, ⊥, 1⟩ * ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩)) := by
    rw [hHg]; exact blk_adj _ _ _ _ _ _ hvE hvE hadj
  have hP0 : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hHb := blk_smulH B.S.H _ _ _ _ _ _ hP0 hHg (blk_HV B X P ψ) hvC
  have hzJ : B.zE ⟨X, ⊥, 1⟩ Z * J = (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * B.zE ⟨X, P, ψ⟩ Z := by
    apply blk_ext; intro x
    apply blk_vE_inj B ⟨X, ⊥, 1⟩
    have h1 := hJ x
    rw [BlockDat.toF_apply, BlockDat.toF_apply] at h1
    have h2 := B.S.basis.equivFun.symm.injective h1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc (B.vE ⟨X, ⊥, 1⟩) (B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩), hvC]
    simpa only [Matrix.mulVec_mulVec] using h2
  have hJi : Function.Injective J.mulVec := by
    intro x y hxy
    have h1 : ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * B.zE ⟨X, P, ψ⟩ Z) *ᵥ x =
        ((B.vPr ⟨X, ⊥, 1⟩ * B.vE ⟨X, P, ψ⟩) * B.zE ⟨X, P, ψ⟩ Z) *ᵥ y := by
      rw [← hzJ, ← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_mulVec]
    have h2 := congrArg (fun w => (B.vPr ⟨X, P, ψ⟩ * B.vE ⟨X, ⊥, 1⟩) *ᵥ w) h1
    simp only [Matrix.mulVec_mulVec] at h2
    rw [← Matrix.mul_assoc, hDC, Matrix.one_mul] at h2
    exact (subspace_image_spec K _ (B.Z0 ⟨X, P, ψ⟩ Z)).1 h2
  obtain ⟨W, hW⟩ := blk_range B ⟨X, ⊥, 1⟩ ⟨X, ⊥, 1⟩ Z hZ _ (goodAt X P ψ) hvE
  obtain ⟨V, hV⟩ := blk_range B ⟨X, ⊥, 1⟩ ⟨X, P, ψ⟩ Z hZ _ (goodAt X P ψ) hvD
  have hPg := BlockDat.Pq_orth (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX
  have hPb := BlockDat.Pq_orth (B := B) (ℓ := ⟨X, P, ψ⟩) (Z := Z) hv0 h hX
  obtain ⟨e1, e2⟩ := blk_transAbs _ _ _ _ _ _ rfl hPg hPb _ _ hDC hEadj _ hHb W hW V hV J hzJ
  exact ⟨hDC, hvC, hvE, ⟨_, e1⟩, e2, hJi⟩

end BlkK

section AtPlace

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem blk_map_smul {a b : ℕ} (σ : K →+* ℂ) (c : K) (M : Matrix (Fin a) (Fin b) K) :
    (c • M).map σ = σ c • M.map σ := by
  ext i j
  simp [Matrix.map_apply, map_mul]

theorem blk_transC (hq : QuotThrough) (σ : K →+* ℂ) {a ng nb dg db : ℕ} (H : Matrix (Fin a) (Fin a) K)
    (vg : Matrix (Fin a) (Fin ng) K) (vb : Matrix (Fin a) (Fin nb) K) (eb : Matrix (Fin a) (Fin a) K)
    (C : Matrix (Fin ng) (Fin nb) K) (D : Matrix (Fin nb) (Fin ng) K) (Hg : Matrix (Fin ng) (Fin ng) K)
    (Hb : Matrix (Fin nb) (Fin nb) K) (Pg : Matrix (Fin dg) (Fin ng) K) (Pb : Matrix (Fin db) (Fin nb) K)
    (N : Matrix (Fin dg) (Fin dg) K) (J : Matrix (Fin dg) (Fin db) K) (k : ℕ) (hk : 0 < k)
    (hHg : Hg = vgᴴ * H * vg) (hHb : Hb = (k : K)⁻¹ • (vbᴴ * H * vb))
    (hvg : ∀ i j, vg i j ∈ cmMax K) (hvb : ∀ i j, vb i j ∈ cmMax K)
    (heb : ∀ i j, eb i j ∈ cmMax K) (hpos : (Hg.map σ).PosDef) (hPg : Function.Surjective (Pg.map σ).mulVec)
    (hPb : Function.Surjective (Pb.map σ).mulVec) (hDC : D * C = 1) (hvC : vg * C = vb)
    (hvE : vg * (C * D) = eb * vg) (hadj : ebᴴ * H = H * eb) (hN : Pg * (C * D) = N * Pg)
    (hJ : Function.Injective J.mulVec) (hPC : Pg * C = J * Pb) :
    quotMetC (Pb.map σ) (Hb.map σ) =
      (((k : ℝ)⁻¹ : ℝ) : ℂ) • ((J.map σ)ᴴ * quotMetC (Pg.map σ) (Hg.map σ) * J.map σ) := by
  have hHgσ : Hg.map σ = (vg.map σ)ᴴ * H.map σ * vg.map σ := by
    rw [hHg, Matrix.map_mul, Matrix.map_mul, blk_cm σ vg hvg]
  have hDCσ : D.map σ * C.map σ = 1 := by
    rw [← Matrix.map_mul, hDC]
    simp [Matrix.map_one]
  have hT : vg.map σ * (C.map σ * D.map σ) = eb.map σ * vg.map σ := by
    simp only [← Matrix.map_mul, hvE]
  have hF : (eb.map σ)ᴴ * H.map σ = H.map σ * eb.map σ := by
    rw [← blk_cm σ eb heb]
    simp only [← Matrix.map_mul, hadj]
  have hEσ : (C.map σ * D.map σ)ᴴ * Hg.map σ = Hg.map σ * (C.map σ * D.map σ) := by
    rw [hHgσ]
    exact blk_adj (vg.map σ) (C.map σ * D.map σ) (C.map σ * D.map σ) (eb.map σ) (eb.map σ) (H.map σ) hT hT hF
  have hNσ : Pg.map σ * (C.map σ * D.map σ) = N.map σ * Pg.map σ := by
    simp only [← Matrix.map_mul, hN]
  have hPCσ : Pg.map σ * C.map σ = J.map σ * Pb.map σ := by
    simp only [← Matrix.map_mul, hPC]
  have hvCσ : vg.map σ * C.map σ = vb.map σ := by
    simp only [← Matrix.map_mul, hvC]
  have hJσ : Function.Injective (J.map σ).mulVec := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' J)
      (LinearMap.ker_eq_bot.mpr (fun a b hab => hJ (by simpa only [Matrix.toLin'_apply] using hab)))
    have hL : LinearMap.toMatrix' g * J = 1 := by
      rw [← LinearMap.toMatrix'_toLin' J, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    intro a b hab
    have h2 := congrArg (fun w => ((LinearMap.toMatrix' g).map σ) *ᵥ w) hab
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hL] at h2
    simpa [Matrix.map_one] using h2
  have key := hq ng nb dg db (Hg.map σ) hpos (Pg.map σ) hPg (C.map σ) (D.map σ) hDCσ hEσ (N.map σ) hNσ
    (Pb.map σ) hPb (J.map σ) hJσ hPCσ
  have hc' : (((k : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by simp [hk.ne']
  have hHbσ : Hb.map σ = (((k : ℝ)⁻¹ : ℝ) : ℂ) • ((C.map σ)ᴴ * Hg.map σ * C.map σ) := by
    rw [hHb, blk_map_smul, Matrix.map_mul, Matrix.map_mul, blk_cm σ vb hvb, hHgσ,
      blk_pull (vg.map σ) (vb.map σ) (C.map σ) (H.map σ) hvCσ]
    congr 1
    simp [map_inv₀, map_natCast]
  unfold quotMetC
  rw [hHbσ, inv_smul_ne _ hc', Matrix.mul_smul, Matrix.smul_mul, inv_smul_ne _ (inv_ne_zero hc'), inv_inv]
  exact congrArg (fun M => (((k : ℝ)⁻¹ : ℝ) : ℂ) • M) key

theorem blk_invC (hu : QuotUnitary) (σ : K →+* ℂ) {a ng dg : ℕ} (H : Matrix (Fin a) (Fin a) K)
    (vg : Matrix (Fin a) (Fin ng) K) (A : Matrix (Fin a) (Fin a) K) (Hg : Matrix (Fin ng) (Fin ng) K)
    (Pg : Matrix (Fin dg) (Fin ng) K) (R R' : Matrix (Fin ng) (Fin ng) K) (ρ : Matrix (Fin dg) (Fin dg) K)
    (hHg : Hg = vgᴴ * H * vg) (hvg : ∀ i j, vg i j ∈ cmMax K)
    (hA : ∀ i j, A i j ∈ cmMax K) (hpos : (Hg.map σ).PosDef) (hPg : Function.Surjective (Pg.map σ).mulVec)
    (hvR : vg * R = A * vg) (hRR : R * R' = 1) (hAu : Aᴴ * H * A = H) (hN : Pg * R = ρ * Pg) :
    (ρ.map σ)ᴴ * quotMetC (Pg.map σ) (Hg.map σ) * ρ.map σ = quotMetC (Pg.map σ) (Hg.map σ) := by
  have hHgσ : Hg.map σ = (vg.map σ)ᴴ * H.map σ * vg.map σ := by
    rw [hHg, Matrix.map_mul, Matrix.map_mul, blk_cm σ vg hvg]
  have hR1 : (R.map σ)ᴴ * (Hg.map σ) * R.map σ = Hg.map σ := by
    rw [hHgσ]
    apply blk_unit (vg.map σ) (R.map σ) (A.map σ) (H.map σ)
    · simp only [← Matrix.map_mul, hvR]
    · rw [← blk_cm σ A hA]
      simp only [← Matrix.map_mul, hAu]
  have hRu : IsUnit (R.map σ).det := by
    have h1 : R.map σ * R'.map σ = 1 := by
      rw [← Matrix.map_mul, hRR]
      simp [Matrix.map_one]
    exact Matrix.isUnit_det_of_right_inverse h1
  exact hu ng dg (Hg.map σ) hpos (Pg.map σ) hPg (R.map σ) hR1 hRu (ρ.map σ)
    (by simp only [← Matrix.map_mul, hN])

theorem blk_metQ {K : Type} [Field K] [NumberField K] {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (H : Matrix (Fin n) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (h : IsQuotMetric P H XQ)
    (v : InfinitePlace K) : metOf (XQ v) = quotMetC (P.map v.embedding) (H.map v.embedding) := by
  unfold metOf quotMetC
  exact (h v).2

end AtPlace

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem blk_invK (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g)) (g : G)
    (ρ : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hρ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (ρ *ᵥ x) = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x)) :
    ∃ RK RK' : Matrix (Fin (B.nV ⟨X, ⊥, 1⟩)) (Fin (B.nV ⟨X, ⊥, 1⟩)) K,
      B.vE ⟨X, ⊥, 1⟩ * RK = B.S.actMat B.r g * B.vE ⟨X, ⊥, 1⟩ ∧ RK * RK' = 1 ∧
        B.Pq ⟨X, ⊥, 1⟩ Z * RK = ρ * B.Pq ⟨X, ⊥, 1⟩ Z := by
  have hcg := blk_cut B hv0 h X hX ⊥ 1
  have hvR := blk_vR (B.vE ⟨X, ⊥, 1⟩) (B.vPr ⟨X, ⊥, 1⟩) _ (B.S.actMat B.r g) hcg.2 (blk_comm B X hX g) hcg.1.1
  have hvR' := blk_vR (B.vE ⟨X, ⊥, 1⟩) (B.vPr ⟨X, ⊥, 1⟩) _ (B.S.actMat B.r g⁻¹) hcg.2 (blk_comm B X hX g⁻¹)
    hcg.1.1
  have hRR := blk_RR (B.vPr ⟨X, ⊥, 1⟩) (B.vE ⟨X, ⊥, 1⟩) _ _ hvR' (B.S.actMat_mul_inv B.r g) hcg.1.1
  have hadj0 := B.S.actMat_adj B.r h.act g⁻¹
  rw [inv_inv] at hadj0
  have hadj := blk_adj (B.vE ⟨X, ⊥, 1⟩) _ _ _ _ B.S.H hvR hvR' hadj0
  rw [← blk_HV_bot] at hadj
  obtain ⟨W, hW⟩ := blk_range B ⟨X, ⊥, 1⟩ ⟨X, ⊥, 1⟩ Z hZ _ (MonoidAlgebra.single g⁻¹ 1)
    (by rw [B.gaMat_single]; exact hvR')
  have hPg := BlockDat.Pq_orth (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX
  have hzρ : B.zE ⟨X, ⊥, 1⟩ Z * ρ = (B.vPr ⟨X, ⊥, 1⟩ * B.S.actMat B.r g * B.vE ⟨X, ⊥, 1⟩) * B.zE ⟨X, ⊥, 1⟩ Z := by
    apply blk_ext; intro x
    apply blk_vE_inj B ⟨X, ⊥, 1⟩
    have h1 := congrArg B.S.basis.equivFun (hρ x)
    rw [BlockDat.toF_apply, BlockDat.toF_apply, LinearEquiv.apply_symm_apply, BlockDat.equivFun_act,
      LinearEquiv.apply_symm_apply] at h1
    have h2 := congrArg (· * B.zE ⟨X, ⊥, 1⟩ Z) hvR
    simp only [Matrix.mul_assoc] at h2
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h1 ⊢
    rw [h2]
    exact h1
  exact ⟨_, _, hvR, hRR, blk_invAbs _ _ _ rfl hPg _ _ hadj W hW ρ hzρ⟩

theorem quot_transfer (hq : QuotThrough) (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (J *ᵥ x) = B.toF ⟨X, P, ψ⟩ Z x) (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, P, ψ⟩ Z) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, P, ψ⟩ Z) v x y =
      (((Nat.card P : ℝ)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (J *ᵥ x) (J *ᵥ y) := by
  obtain ⟨hDC, hvC, hvE, ⟨NK, hN⟩, hPC, hJi⟩ := blk_transK B hv0 h X hX P ψ Z hZ J hJ
  have key := blk_transC hq v.embedding B.S.H (B.vE ⟨X, ⊥, 1⟩) (B.vE ⟨X, P, ψ⟩) (B.S.gaMat B.r (goodAt X P ψ))
    _ _ (B.HV ⟨X, ⊥, 1⟩) (B.HV ⟨X, P, ψ⟩) (B.Pq ⟨X, ⊥, 1⟩ Z) (B.Pq ⟨X, P, ψ⟩ Z) NK J (Nat.card P) Nat.card_pos
    (blk_HV_bot B X) (blk_HV B X P ψ) (BlockDat.vE_rat (B := B) (ℓ := ⟨X, ⊥, 1⟩) hv0 h hX)
    (BlockDat.vE_rat (B := B) (ℓ := ⟨X, P, ψ⟩) hv0 h hX)
    (gaMat_rat B.S B.r h.actRat (goodAt X P ψ) (good_at_spec K v0 hv0 G X hX P ψ).rat)
    (BlockDat.HV_pos (B := B) (ℓ := ⟨X, ⊥, 1⟩) hv0 h hX v)
    (map_surj _ _ (BlockDat.Pq_surj (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX))
    (map_surj _ _ (BlockDat.Pq_surj (B := B) (ℓ := ⟨X, P, ψ⟩) (Z := Z) hv0 h hX))
    hDC hvC hvE (blk_adjE B hv0 h X hX P ψ) hN hJi hPC
  refine blk_maj (B.XQ ⟨X, P, ψ⟩ Z) (B.XQ ⟨X, ⊥, 1⟩ Z) v J _ ?_ x y
  rw [blk_metQ _ _ _ (BlockDat.XQ_quot (B := B) (ℓ := ⟨X, P, ψ⟩) (Z := Z) hv0 h hX) v,
    blk_metQ _ _ _ (BlockDat.XQ_quot (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX) v, key]

theorem quot_invariant (hu : QuotUnitary) (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g)) (g : G)
    (ρ : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hρ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (ρ *ᵥ x) = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x)) (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (ρ *ᵥ x) (ρ *ᵥ y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v x y := by
  obtain ⟨RK, RK', hvR, hRR, hN⟩ := blk_invK B hv0 h X hX Z hZ g ρ hρ
  have key := blk_invC hu v.embedding B.S.H (B.vE ⟨X, ⊥, 1⟩) (B.S.actMat B.r g) (B.HV ⟨X, ⊥, 1⟩) (B.Pq ⟨X, ⊥, 1⟩ Z)
    RK RK' ρ (blk_HV_bot B X) (BlockDat.vE_rat (B := B) (ℓ := ⟨X, ⊥, 1⟩) hv0 h hX) (h.actRat g)
    (BlockDat.HV_pos (B := B) (ℓ := ⟨X, ⊥, 1⟩) hv0 h hX v)
    (map_surj _ _ (BlockDat.Pq_surj (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX)) hvR hRR
    (B.S.actMat_unitary B.r h.act g) hN
  have hm := blk_metQ _ _ _ (BlockDat.XQ_quot (B := B) (ℓ := ⟨X, ⊥, 1⟩) (Z := Z) hv0 h hX) v
  have e := blk_maj (B.XQ ⟨X, ⊥, 1⟩ Z) (B.XQ ⟨X, ⊥, 1⟩ Z) v ρ 1 (by rw [one_smul, hm, key]) x y
  rw [e, one_mul]

theorem quotThrough_holds : QuotThrough := by
  exact fun n m d d' A hA P hP C D hDC hE N hN P' hP' J hJ hPC =>
    quotMetC_through A hA P hP C D hDC hE N hN P' hP' J hJ hPC

theorem quotUnitary_holds : QuotUnitary := by
  exact fun n d A hA P hP R hR hRu N hN => quotMetC_unitary A hA P hP R hR hRu N hN

theorem quot_transfer' (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms)
    (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (J *ᵥ x) = B.toF ⟨X, P, ψ⟩ Z x) (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, P, ψ⟩ Z) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, P, ψ⟩ Z) v x y =
      (((Nat.card P : ℝ)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (J *ᵥ x) (J *ᵥ y) := by
  exact quot_transfer quotThrough_holds B hv0 h X hX P ψ Z hZ J hJ v x y

theorem quot_invariant' (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g)) (g : G)
    (ρ : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hρ : ∀ x, B.toF ⟨X, ⊥, 1⟩ Z (ρ *ᵥ x) = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x)) (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (ρ *ᵥ x) (ρ *ᵥ y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v x y := by
  exact quot_invariant quotUnitary_holds B hv0 h X hX Z hZ g ρ hρ v x y

end Main

end Formalism.IndefR.CxPass.BlockMetrics

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

def TransferS : Prop := ∀ (B : BlockDat K G Pl0) {v0 : InfinitePlace K}, IsConjAt v0 → ∀ {s : ℕ}, B.Ok s →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms),
    (∀ g, Z ≤ Z.comap (B.r g)) → ∀ (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K),
    (∀ x, B.toF ⟨X, ⊥, 1⟩ Z (J *ᵥ x) = B.toF ⟨X, P, ψ⟩ Z x) → ∀ (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, P, ψ⟩ Z) → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, P, ψ⟩ Z) v x y =
      (((Nat.card P : ℝ)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (J *ᵥ x) (J *ᵥ y)

def InvS : Prop := ∀ (B : BlockDat K G Pl0) {v0 : InfinitePlace K}, IsConjAt v0 → ∀ {s : ℕ}, B.Ok s →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (Z : Submodule K B.S.Forms), (∀ g, Z ≤ Z.comap (B.r g)) →
    ∀ (g : G) (ρ : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K),
    (∀ x, B.toF ⟨X, ⊥, 1⟩ Z (ρ *ᵥ x) = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x)) → ∀ (v : InfinitePlace K) (x y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v (ρ *ᵥ x) (ρ *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ⟨X, ⊥, 1⟩ Z) v x y

theorem transferS_holds : TransferS (K := K) (G := G) (Pl0 := Pl0) := by
  exact fun B v0 hv0 s h X hX P ψ Z hZ J hJ v x y => BlockMetrics.quot_transfer' B hv0 h X hX P ψ Z hZ J hJ v x y

theorem invS_holds : InvS (K := K) (G := G) (Pl0 := Pl0) := by
  exact fun B v0 hv0 s h X hX Z hZ g ρ hρ v x y => BlockMetrics.quot_invariant' B hv0 h X hX Z hZ g ρ hρ v x y

theorem side_lv (b : Bool) :
    lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b = I.A.side (I.lvP b) (I.lvψ b) I.X.zs := by
  cases b <;> rfl

theorem side_g : lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false = I.A.side ⊥ 1 I.X.zs := rfl

theorem toR_cr (b : Bool) (t : I.A.fam.base.Tup) :
    HEq (I.cr.toR I.X.zs b t) ((I.A.fam.R t).toF (I.A.fam.lvl (I.lvP b) (I.lvψ b)) (I.X.zs.Z t)) := by
  cases b <;> exact HEq.rfl

theorem toR_cg (t : I.A.fam.base.Tup) :
    I.cg.toR I.X.zs false t = (I.A.fam.R t).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z t) := rfl

theorem Jm_eq (b : Bool) : I.Jm b = I.Jt b I.A.fam.base.μ0 := rfl

theorem iC_cpt {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)
    (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, CxData.iC, lin_apply, cpt]

theorem gramE_unit' {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)
    (h1 : Function.Injective (X.iC cr b Bs.μ0)) (hn : 0 < X.nP b) : IsUnit (frameOf (X.gramE cr b)).det :=
  frame_gram_smul_unit _ (li_of_lin_injective (by rw [lin_basis]; exact h1)) _ (inv_pos.mpr hn)

theorem pFrames : I.PFrames := by
  intro s h v
  have hW := I.A.side_WF h.ok ⊥ 1 I.X.zs h.stable h.inBlock h.sep
  have hu : IsUnit (frameOf ((prin I.X).gramE I.cg false)).det :=
    gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)
  exact (rowXE_spec (Df := I.A.side ⊥ 1 I.X.zs) hW _ hu I.X.κ h.h4pos.1 (fun j p v => I.X.lam j I.A.fam.base.μ0 p v)
    (fun j p v => h.h4pos.2.1 j _ p v)).1 v

theorem exists_toF_act (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hrow : B.Ok s)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZg : ∀ g, Z ≤ Z.comap (B.r g))
    (g : G) (x : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    ∃ y, B.toF ⟨X, ⊥, 1⟩ Z y = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) := by
  have h1 : B.toF ⟨X, ⊥, 1⟩ Z x ∈ B.goodF X := by
    have : B.zE ⟨X, ⊥, 1⟩ Z *ᵥ x ∈ B.inV0 ⟨X, ⊥, 1⟩ (B.goodF X) := by
      rw [B.good_part_coordinates_good_eq_top ⟨X, ⊥, 1⟩ hv0 hX]; trivial
    rw [B.mem_goodPart_iff] at this
    exact this
  have h2 : B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) ∈ B.goodF X := (B.goodF_stable hv0 hrow hX).2 g h1
  have h3 : B.toF ⟨X, ⊥, 1⟩ Z x ∈ Z := by
    have := B.zE_mem ⟨X, ⊥, 1⟩ Z x
    rw [BlockDat.Z0, B.mem_goodPart_iff] at this
    exact this
  have h4 : B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) ∈ Z := hZg g h3
  obtain ⟨u, hu⟩ := B.exists_vE_of_fix ⟨X, ⊥, 1⟩ ((B.mem_goodF hv0 hX _).1 h2)
  have hu0 : u ∈ B.Z0 ⟨X, ⊥, 1⟩ Z := by rw [BlockDat.Z0, B.mem_goodPart_iff, hu]; exact h4
  obtain ⟨y, hy⟩ := B.exists_zE ⟨X, ⊥, 1⟩ Z hu0
  exact ⟨y, by rw [BlockDat.toF_apply, hy, hu]⟩

variable {I} in
theorem Z_stable_g {s : ℕ} (h : I.Hyp s) (g : G) :
    I.X.zs.Z I.A.fam.μ0 ≤ (I.X.zs.Z I.A.fam.μ0).comap ((I.A.fam.R I.A.fam.μ0).r g) := fun _ hz =>
  h.stable.1 I.A.fam.μ0 (Sum.inr g) (Submodule.mem_map_of_mem hz)

variable {I} in
theorem toF_rho (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.ρf g *ᵥ x) =
      (I.A.fam.R I.A.fam.μ0).r g ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x) := by
  obtain ⟨y, hty⟩ := exists_toF_act (I.A.fam.R I.A.fam.μ0) h.ok.conj (h.ok.what₂ _) I.A.fam.X h.ok.irr
    (I.X.zs.Z I.A.fam.μ0) (fun g => Z_stable_g h g) g x
  have key : I.iCg (cpt I.A.fam.base.v0.embedding (I.ρf g *ᵥ x)) = I.iCg (cpt I.A.fam.base.v0.embedding y) := by
    rw [(hρ s h).2.2 g x]
    have e1 : I.iCg (cpt I.A.fam.base.v0.embedding x) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 x
    have e2 : I.iCg (cpt I.A.fam.base.v0.embedding y) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) y)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 y
    rw [e1, e2]
    erw [hty]
    exact (h.gequiv I.A.fam.μ0 g _).symm
  have hxy := cpt_injective _ (h.h2g.1 key)
  exact (congrArg (fun z => (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) z) hxy).trans hty

theorem partPr_map {Bs : DefBase K} (D1 D2 : DefSide Bs) (h1 : D1.WF) (h2 : D2.WF)
    (M : Matrix (Fin (D2.dQ Bs.μ0)) (Fin (D1.dQ Bs.μ0)) K)
    (hM : ∀ p x, x ∈ D1.Qp Bs.μ0 p → M *ᵥ x ∈ D2.Qp Bs.μ0 p) (p : Bs.Ix) (x : Fin (D1.dQ Bs.μ0) → K) :
    partPr D2 Bs.μ0 p *ᵥ (M *ᵥ x) = M *ᵥ (partPr D1 Bs.μ0 p *ᵥ x) := by
  conv_lhs => rw [← sum_partPr_mulVec D1 Bs.μ0 h1.Qp_indep h1.Qp_top x]
  rw [Matrix.mulVec_sum, Matrix.mulVec_sum, Finset.sum_eq_single p]
  · exact partPr_self D2 Bs.μ0 h2.Qp_indep h2.Qp_top (hM p _ (partPr_mem D1 Bs.μ0 h1.Qp_indep h1.Qp_top p x))
  · intro q _ hqp
    exact partPr_other D2 Bs.μ0 h2.Qp_indep h2.Qp_top (hM q _ (partPr_mem D1 Bs.μ0 h1.Qp_indep h1.Qp_top q x))
      (Ne.symm hqp)
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem rowXE_map {Bs : DefBase K} (D1 D2 : DefSide Bs) (h1 : D1.WF) (h2 : D2.WF)
    (Y1 : Matrix (Fin (D1.dQ Bs.μ0)) (Fin (D1.dQ Bs.μ0)) ℂ) (hY1 : IsUnit Y1.det)
    (Y2 : Matrix (Fin (D2.dQ Bs.μ0)) (Fin (D2.dQ Bs.μ0)) ℂ) (hY2 : IsUnit Y2.det)
    (κ : InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (lam : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (hlam : ∀ j p v, 0 < lam j p v) (M : Matrix (Fin (D2.dQ Bs.μ0)) (Fin (D1.dQ Bs.μ0)) K)
    (hM : ∀ p x, x ∈ D1.Qp Bs.μ0 p → M *ᵥ x ∈ D2.Qp Bs.μ0 p) (c : ℂ) (v : InfinitePlace K) (hv : v ≠ Bs.v0)
    (hq : ∀ x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (D1.XQ Bs.μ0) v x y =
      c * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (D2.XQ Bs.μ0) v (M *ᵥ x) (M *ᵥ y))
    (x y : Fin (D1.dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (rowXE D1 Y1 κ lam) v x y =
      c * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (rowXE D2 Y2 κ lam) v (M *ᵥ x) (M *ᵥ y) := by
  rw [(rowXE_spec (Df := D1) h1 Y1 hY1 κ hκ lam hlam).2.2 v hv x y,
    (rowXE_spec (Df := D2) h2 Y2 hY2 κ hκ lam hlam).2.2 v hv (M *ᵥ x) (M *ᵥ y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [partPr_map D1 D2 h1 h2 M hM p x, partPr_map D1 D2 h1 h2 M hM p y, hq]
  ring

variable {I} in
theorem wf_lv {s : ℕ} (h : I.Hyp s) (b : Bool) : (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).WF := by
  rw [side_lv]; exact I.A.side_WF h.ok _ _ _ h.stable h.inBlock h.sep

variable {I} in
theorem wf_g {s : ℕ} (h : I.Hyp s) : (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).WF :=
  I.A.side_WF h.ok ⊥ 1 _ h.stable h.inBlock h.sep

theorem mem_part_iff (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (S : Pl0 → Polynomial K)
    (y : Fin (B.dZ ℓ Z) → K) : y ∈ B.part ℓ Z S ↔ B.toF ℓ Z y ∈ B.partF S := by
  show B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ y) ∈
      (B.partF S).map (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) ↔ _
  exact Submodule.mem_map_equiv (e := B.S.basis.equivFun) (p := B.partF S)

variable {I} in
theorem Jm_parts (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool) (p : I.A.fam.base.Ix)
    (x : Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A.fam.base.μ0) → K)
    (hx : x ∈ (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).Qp I.A.fam.base.μ0 p) :
    I.Jm b *ᵥ x ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A.fam.base.μ0 p := by
  cases b
  · refine (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm false *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm false *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h false I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  · refine (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm true *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm true *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h true I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx

variable {I} in
theorem quot_lv (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool)
    (v : InfinitePlace K)
    (x y : Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A.fam.base.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).XQ I.A.fam.base.μ0) v x y =
      (((Nat.card (I.lvP b) : ℝ)⁻¹ : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).XQ I.A.fam.base.μ0) v
          (I.Jm b *ᵥ x) (I.Jm b *ᵥ y) := by
  cases b
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.conj (h.ok.what₂ _) I.A.fam.X h.ok.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm false) (hJt s h false I.A.fam.μ0).2.1 v x y
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.conj (h.ok.what₂ _) I.A.fam.X h.ok.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm true) (hJt s h true I.A.fam.μ0).2.1 v x y

theorem majorant_at_base_eq_scaled_inner {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (hW : (lv (fc X.zs) b).WF) (h2 : Function.Injective (X.iC cr b Bs.μ0)) (hn : 0 < X.nP b) (hκ : ∀ v, 0 < X.κ v)
    (hlam : ∀ j p v, 0 < X.lam j Bs.μ0 p v) (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y =
      (((X.nP b)⁻¹ : ℝ) : ℂ) * ⟪X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x), X.iC cr b Bs.μ0 (cpt Bs.v0.embedding y)⟫_ℂ := by
  have hX : X.XE cr b Bs.v0 = frameOf (X.gramE cr b) :=
    (rowXE_spec (Df := lv (fc X.zs) b) hW _ (gramE_unit' X cr b h2 hn) X.κ hκ (fun j p v => X.lam j Bs.μ0 p v)
      (fun j p v => hlam j p v)).2.1
  rw [majAt_gram_smul (X.XE cr b) Bs.v0 (fun i => X.iC cr b Bs.μ0 (Pi.single i 1))
    (li_of_lin_injective (by rw [lin_basis]; exact h2)) _ (inv_pos.mpr hn) hX, lin_basis]

variable {I} in
theorem majorant_at_base_eq_inner {s : ℕ} (h : I.Hyp s) (x y : Fin I.Sg.D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE I.A.fam.base.v0 x y =
      ⟪I.iCg (cpt I.A.fam.base.v0.embedding x), I.iCg (cpt I.A.fam.base.v0.embedding y)⟫_ℂ := by
  have e := majorant_at_base_eq_scaled_inner (prin I.X) I.cg false (wf_g h) h.h2g.1 (show (0 : ℝ) < 1 by norm_num) h.h4pos.1
    (fun j p v => h.h4pos.2.1 j _ p v) x y
  have e1 : (prin I.X).nP false = 1 := rfl
  rw [e1, inv_one, Complex.ofReal_one, one_mul] at e
  exact e

variable {I} in
theorem majorant_at_base_eq_inner_of_package {s : ℕ} (h : I.Hyp s) (b : Bool) (x y : Fin (I.Sb b).D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE I.A.fam.base.v0 x y =
      (((I.X.nP b)⁻¹ : ℝ) : ℂ) *
        ⟪I.X.iC I.cr b I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x),
          I.X.iC I.cr b I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding y)⟫_ℂ :=
  majorant_at_base_eq_scaled_inner I.X I.cr b (wf_lv h b) (h.h2 b).1 (h.h4pos.2.2 b) h.h4pos.1 (fun j p v => h.h4pos.2.1 j _ p v) x y

variable {I} in
theorem nP_eq_card_lvP {s : ℕ} (h : I.Hyp s) (b : Bool) : I.X.nP b = (Nat.card (I.lvP b) : ℝ) := by
  cases b
  · exact h.np0
  · exact h.np1

theorem pMet_core (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hsc : ∀ {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (c : ℝ), 0 < c → ∀ (v : InfinitePlace K) (x y : Fin n → K),
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (Formalism.BranchingDeterminantCap.scaleFrame c X) v x y =
        (((c ^ 2)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y)
    (hJt : I.PJt) (hJ : I.PJ) : I.PMet := by
  intro s h b v x y
  have hcard : (0 : ℝ) < (Nat.card (I.lvP b) : ℝ) := by exact_mod_cast Nat.card_pos
  rw [hsc _ _ (Real.sqrt_pos.2 hcard), Real.sq_sqrt hcard.le]
  by_cases hv : v = I.A.fam.base.v0
  · subst hv
    rw [majorant_at_base_eq_inner_of_package h b, majorant_at_base_eq_inner h, nP_eq_card_lvP h b]
    congr 1
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hJ s h b).1 x) ((hJ s h b).1 y)).symm
  · exact rowXE_map (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b)
      (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_lv h b) (wf_g h) _
      (gramE_unit' I.X I.cr b (h.h2 b).1 (h.h4pos.2.2 b)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A.fam.base.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.Jm b)
      (fun p x hx => Jm_parts hJt h b p x hx) _ v hv (quot_lv hT hJt h b v) x y

variable {I} in
theorem rho_parts (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (p : I.A.fam.base.Ix)
    (x : Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A.fam.base.μ0) → K)
    (hx : x ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A.fam.base.μ0 p) :
    I.ρf g *ᵥ x ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A.fam.base.μ0 p := by
  have hx' := (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  refine (mem_part_iff (I.A.fam.R I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.ρf g *ᵥ x)).2 ?_
  rw [toF_rho hρ h g x]
  exact Formalism.L2.Col.eigSum_le_comap (fun k => (h.ok.what₂ I.A.fam.μ0).opG k g) _ hx'

theorem pUni_core (hI : InvS (K := K) (G := G) (Pl0 := Pl0)) (hρ : I.PRho) : I.PUni := by
  intro s h v g x y
  by_cases hv : v = I.A.fam.base.v0
  · subst hv
    rw [majorant_at_base_eq_inner h, majorant_at_base_eq_inner h]
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hρ s h).2.2 g x) ((hρ s h).2.2 g y)).trans (h.gunit g _ _)
  · have e := rowXE_map (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false)
      (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_g h) (wf_g h) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A.fam.base.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.ρf g)
      (fun p x hx => rho_parts hρ h g p x hx) 1 v hv
      (fun x y => by
        rw [one_mul]
        exact (hI (I.A.fam.R I.A.fam.μ0) h.ok.conj (h.ok.what₂ _) I.A.fam.X h.ok.irr (I.X.zs.Z I.A.fam.μ0)
          (fun g => Z_stable_g h g) g (I.ρf g) (toF_rho hρ h g) v x y).symm) x y
    rw [one_mul] at e
    exact e.symm

theorem pMet_of (hJt : I.PJt) (hJ : I.PJ) : I.PMet := by
  exact I.pMet_core transferS_holds (fun X c hc v x y => BlockMetrics.majAt_scaleFrame X c hc v x y) hJt hJ

theorem pUni_of (_hJt : I.PJt) (hρ : I.PRho) : I.PUni := by
  exact I.pUni_core invS_holds hρ

end In

end Formalism.IndefR.CxPass
