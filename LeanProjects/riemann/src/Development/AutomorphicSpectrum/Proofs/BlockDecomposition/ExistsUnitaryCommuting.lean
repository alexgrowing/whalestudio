import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.CompanionTheory.WittIwasawa

section Eigen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def halfProj (T : V →ₗ[ℂ] V) (s : ℂ) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • (LinearMap.id + s • T)

theorem halfProj_apply (T : V →ₗ[ℂ] V) (s : ℂ) (x : V) :
    halfProj T s x = (1 / 2 : ℂ) • (x + s • T x) := rfl

theorem map_halfProj {T : V →ₗ[ℂ] V} (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs2 : s * s = 1) (x : V) :
    T (halfProj T s x) = s • halfProj T s x := by
  have e : (s * s) • T x = T x := by rw [hs2, one_smul]
  simp only [halfProj_apply, map_smul, map_add, hT2]
  linear_combination (norm := module) (-1 / 2 : ℂ) • e

theorem halfProj_map {T : V →ₗ[ℂ] V} (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs2 : s * s = 1) (x : V) :
    halfProj T s (T x) = s • halfProj T s x := by
  have e : (s * s) • T x = T x := by rw [hs2, one_smul]
  simp only [halfProj_apply, hT2]
  linear_combination (norm := module) (-1 / 2 : ℂ) • e

theorem inner_halfProj {T : V →ₗ[ℂ] V} (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs : star s = s) (hs2 : s * s = 1) (x y : V) :
    ⟪halfProj T s x, halfProj T s y⟫_ℂ = (1 / 2 : ℂ) * (⟪x, y⟫_ℂ + s * ⟪x, T y⟫_ℂ) := by
  have hs' : (starRingEnd ℂ) s = s := hs
  simp only [halfProj_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    hs', hT x, hT2, map_div₀, map_one, map_ofNat]
  linear_combination (1 / 4 : ℂ) * ⟪x, y⟫_ℂ * hs2

variable [FiniteDimensional ℂ V]

theorem exists_half {α : Type*} {T : V →ₗ[ℂ] V} (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs : star s = s) (hs2 : s * s = 1) (f g : α → V)
    (h1 : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ)
    (h2 : ∀ a b, ⟪f a, T (f b)⟫_ℂ = ⟪g a, T (g b)⟫_ℂ) :
    ∃ v : V →ₗ[ℂ] V, (∀ x y, ⟪v x, v y⟫_ℂ = ⟪halfProj T s x, halfProj T s y⟫_ℂ) ∧
      (∀ x, T (v x) = s • v x) ∧ (∀ x, v (T x) = s • v x) ∧
      ∀ a, v (f a) = halfProj T s (g a) := by
  set W : Submodule ℂ V := LinearMap.ker (T - s • LinearMap.id) with hW
  have hmem : ∀ x, halfProj T s x ∈ W := fun x => by
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, map_halfProj hT2 hs2]
    simp
  let Q : V →ₗ[ℂ] W := LinearMap.codRestrict W (halfProj T s) hmem
  have hQ : ∀ x, (Q x : V) = halfProj T s x := fun x => rfl
  obtain ⟨w, hw⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.exists_linearIsometryEquiv_of_inner_eq
    (fun a => Q (f a)) (fun a => Q (g a)) (fun a b => by
      rw [Submodule.coe_inner, Submodule.coe_inner, hQ, hQ, hQ, hQ,
        inner_halfProj hT hT2 hs hs2, inner_halfProj hT hT2 hs hs2, h1, h2])
  refine ⟨W.subtype ∘ₗ w.toLinearEquiv.toLinearMap ∘ₗ Q, fun x y => ?_, fun x => ?_, fun x => ?_,
    fun a => ?_⟩
  · change ⟪(w (Q x) : V), (w (Q y) : V)⟫_ℂ = _
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, hQ, hQ]
  · change T (w (Q x) : V) = s • (w (Q x) : V)
    have := LinearMap.mem_ker.1 (w (Q x)).2
    rw [LinearMap.sub_apply] at this
    simpa [sub_eq_zero] using this
  · have : Q (T x) = s • Q x := Subtype.ext (by
      rw [hQ, Submodule.coe_smul, hQ, halfProj_map hT2 hs2])
    change (w (Q (T x)) : V) = s • (w (Q x) : V)
    rw [this, map_smul, Submodule.coe_smul]
  · change (w (Q (f a)) : V) = _
    rw [hw a, hQ]

theorem exists_commuting_of_gram {α : Type*} (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (hT2 : ∀ x, T (T x) = x) (f g : α → V)
    (h1 : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ)
    (h2 : ∀ a b, ⟪f a, T (f b)⟫_ℂ = ⟪g a, T (g b)⟫_ℂ) :
    ∃ u : V →ₗ[ℂ] V, (∀ x y, ⟪u x, u y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ (∀ x, u (T x) = T (u x)) ∧
      ∀ a, u (f a) = g a := by
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_half hT hT2 (s := 1) (by simp) (by simp) f g h1 h2
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := exists_half hT hT2 (s := -1) (by simp) (by simp) f g h1 h2
  have cross : ∀ x y, ⟪v x, w y⟫_ℂ = 0 := fun x y => by
    have e := hT (v x) (w y)
    rw [hv2, hw2, one_smul, inner_smul_right] at e
    have : (2 : ℂ) * ⟪v x, w y⟫_ℂ = 0 := by linear_combination e
    simpa using this
  have cross' : ∀ x y, ⟪w x, v y⟫_ℂ = 0 := fun x y => by
    rw [← inner_conj_symm, cross, map_zero]
  refine ⟨v + w, fun x y => ?_, fun x => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, inner_add_left, inner_add_right, cross, cross', hv1, hw1]
    rw [inner_halfProj hT hT2 (by simp) (by simp), inner_halfProj hT hT2 (by simp) (by simp)]
    ring
  · simp only [LinearMap.add_apply, map_add, hv2, hv3, hw2, hw3]
  · simp only [LinearMap.add_apply, hv4, hw4, halfProj_apply]
    module

end Eigen

section Columns

variable {n : ℕ} {κ : Type*}

noncomputable def col (A : Matrix (Fin n) κ ℂ) (a : κ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => A i a)

theorem gram_col {κ' : Type*} (A : Matrix (Fin n) κ ℂ) (B : Matrix (Fin n) κ' ℂ) (a : κ) (b : κ') :
    (Aᴴ * B) a b = ⟪col A a, col B b⟫_ℂ := by
  simp [col, Matrix.mul_apply, PiLp.inner_apply, mul_comm]

theorem toEuclideanLin_col (M : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) κ ℂ) (a : κ) :
    Matrix.toEuclideanLin M (col A a) = col (M * A) a := by
  ext i
  simp [col, Matrix.toEuclideanLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem col_injective {A B : Matrix (Fin n) κ ℂ} (h : ∀ a, col A a = col B a) : A = B := by
  ext i a
  simpa [col] using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) (h a)

end Columns

theorem exists_unitary_commuting {n r : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (hT2 : T * T = 1) (A A' : Matrix (Fin n) (Fin r) ℂ) (h1 : Aᴴ * A = A'ᴴ * A')
    (h2 : Aᴴ * (T * A) = A'ᴴ * (T * A')) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * T = T * U ∧ U * A = A' := by
  have hinv : ∀ x, Matrix.toEuclideanLin T (Matrix.toEuclideanLin T x) = x := fun x => by
    have e : ∀ y : EuclideanSpace ℂ (Fin n), y = col (Matrix.of fun i (_ : Unit) => y i) () :=
      fun y => by ext i; simp [col]
    rw [e x, toEuclideanLin_col, toEuclideanLin_col, ← Matrix.mul_assoc, hT2, Matrix.one_mul]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_commuting_of_gram (Matrix.toEuclideanLin T)
    (fun x y => (Matrix.isHermitian_iff_isSymmetric.1 hT) x y) hinv (col A) (col A')
    (fun a b => by rw [← gram_col, ← gram_col, h1])
    (fun a b => by rw [toEuclideanLin_col, toEuclideanLin_col, ← gram_col, ← gram_col, h2])
  set U : Matrix (Fin n) (Fin n) ℂ := Matrix.toEuclideanLin.symm u with hUdef
  have hU : ∀ x, u x = Matrix.toEuclideanLin U x := fun x => by simp [hUdef]
  have hcol : ∀ a, col U a = u (col (1 : Matrix (Fin n) (Fin n) ℂ) a) := fun a => by
    rw [hU, toEuclideanLin_col, Matrix.mul_one]
  refine ⟨U, ?_, col_injective fun a => ?_, col_injective fun a => ?_⟩
  · ext a b
    rw [gram_col, hcol, hcol, hu1, ← gram_col]
    simp
  · rw [← toEuclideanLin_col, ← toEuclideanLin_col, ← hU, hcol, ← hu2, toEuclideanLin_col,
      Matrix.mul_one]
  · rw [← toEuclideanLin_col, ← hU, hu3]

theorem exists_mem_K {n r : ℕ} (J P : Matrix (Fin n) (Fin n) ℂ) (X X' : Matrix (Fin n) (Fin r) ℂ)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hP : P.PosDef) (hPJ : P * J⁻¹ * P = J)
    (h1 : Xᴴ * P * X = X'ᴴ * P * X') (h2 : Xᴴ * J * X = X'ᴴ * J * X') :
    ∃ m mi : Matrix (Fin n) (Fin n) ℂ, m * mi = 1 ∧ mi * m = 1 ∧ mᴴ * J * m = J ∧
      mᴴ * P * m = P ∧ m * X = X' := by
  obtain ⟨R, -, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hP
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJH : (J⁻¹)ᴴ = J⁻¹ := (hJ.inv).eq
  set T : Matrix (Fin n) (Fin n) ℂ := R * J⁻¹ * Rᴴ with hTdef
  have hTH : T.IsHermitian := by
    simp only [IsHermitian, hTdef, conjTranspose_mul, conjTranspose_conjTranspose, hJH,
      Matrix.mul_assoc]
  have hPW : Rᴴ * (R * (J⁻¹ * P * J⁻¹)) = 1 := by
    rw [← Matrix.mul_assoc, hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJ, hJi]
  have hT2 : T * T = 1 := by
    have := mul_eq_one_comm.1 hPW
    calc T * T = R * J⁻¹ * (Rᴴ * R) * J⁻¹ * Rᴴ := by simp only [hTdef, Matrix.mul_assoc]
      _ = R * (J⁻¹ * P * J⁻¹) * Rᴴ := by rw [hR]; simp only [Matrix.mul_assoc]
      _ = 1 := this
  have hJT : Rᴴ * T * R = J := by
    calc Rᴴ * T * R = (Rᴴ * R) * J⁻¹ * (Rᴴ * R) := by simp only [hTdef, Matrix.mul_assoc]
      _ = J := by rw [hR, hPJ]
  have hgram : ∀ Z : Matrix (Fin n) (Fin r) ℂ, (R * Z)ᴴ * (R * Z) = Zᴴ * P * Z := fun Z => by
    rw [conjTranspose_mul, ← hR]; simp only [Matrix.mul_assoc]
  have hgramT : ∀ Z : Matrix (Fin n) (Fin r) ℂ, (R * Z)ᴴ * (T * (R * Z)) = Zᴴ * J * Z := fun Z => by
    rw [conjTranspose_mul, ← hJT]; simp only [Matrix.mul_assoc]
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_commuting T hTH hT2 (R * X) (R * X')
    (by rw [hgram, hgram, h1]) (by rw [hgramT, hgramT, h2])
  have hU1' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU1
  have hUT : Uᴴ * T * U = T := by rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hconj : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (R⁻¹ * U * R)ᴴ * (Rᴴ * M * R) * (R⁻¹ * U * R) = Rᴴ * (Uᴴ * M * U) * R := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    calc Rᴴ * (Uᴴ * (R⁻¹)ᴴ) * (Rᴴ * M * R) * (R⁻¹ * U * R)
        = Rᴴ * Uᴴ * ((R⁻¹)ᴴ * Rᴴ) * M * (R * R⁻¹) * U * R := by simp only [Matrix.mul_assoc]
      _ = Rᴴ * (Uᴴ * M * U) * R := by rw [hRiH, hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨R⁻¹ * U * R, R⁻¹ * Uᴴ * R, ?_, ?_, ?_, ?_, ?_⟩
  · calc R⁻¹ * U * R * (R⁻¹ * Uᴴ * R) = R⁻¹ * U * (R * R⁻¹) * Uᴴ * R := by
          simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (U * Uᴴ) * R := by rw [hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hU1', Matrix.mul_one, hRi]
  · calc R⁻¹ * Uᴴ * R * (R⁻¹ * U * R) = R⁻¹ * Uᴴ * (R * R⁻¹) * U * R := by
          simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (Uᴴ * U) * R := by rw [hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hRi]
  · have := hconj T
    rwa [hJT, hUT, hJT] at this
  · have := hconj 1
    rw [Matrix.mul_one, hR, Matrix.mul_one, hU1, Matrix.mul_one, hR] at this
    exact this
  · calc R⁻¹ * U * R * X = R⁻¹ * (U * (R * X)) := by simp only [Matrix.mul_assoc]
      _ = X' := by rw [hU3, ← Matrix.mul_assoc, hRi, Matrix.one_mul]

theorem iwasawa_witt_flag : ∀ (n r : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ), J.IsHermitian → IsUnit J.det → Xᴴ * J * X = 0 →
    Yᴴ * J * Y = 0 → Xᴴ * J * Y = 1 → P.PosDef → P * J⁻¹ * P = J → P * X = J * Y →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * J * g = J →
    ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J * p = J ∧ kᴴ * J * k = J ∧ kᴴ * P * k = P ∧
      g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X = X * B := by
  intro n r J P X Y hJ hJu hXX _ hXY hP hPJ hPX g hg
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJH : Jᴴ = J := hJ.eq

  set gi : Matrix (Fin n) (Fin n) ℂ := J⁻¹ * gᴴ * J with hgi
  have hgig : gi * g = 1 := by
    calc gi * g = J⁻¹ * (gᴴ * J * g) := by simp only [hgi, Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJi]
  have hggi : g * gi = 1 := mul_eq_one_comm.1 hgig
  have hgiH : giᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hggi, conjTranspose_one]
  have hgiJ : giᴴ * J * gi = J := by
    calc giᴴ * J * gi = giᴴ * (gᴴ * J * g) * gi := by rw [hg]
      _ = (giᴴ * gᴴ) * J * (g * gi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hgiH, hggi, Matrix.one_mul, Matrix.mul_one]

  set Z : Matrix (Fin n) (Fin r) ℂ := gi * X with hZ
  have hZJ : Zᴴ * J * Z = 0 := by
    calc Zᴴ * J * Z = Xᴴ * (giᴴ * J * gi) * X := by
          simp only [hZ, conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hgiJ, hXX]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hJH, conjTranspose_one,
      Matrix.mul_assoc] using this
  have hLZ : (Yᴴ * J * g) * Z = 1 := by
    calc (Yᴴ * J * g) * Z = Yᴴ * J * (g * gi) * X := by simp only [hZ, Matrix.mul_assoc]
      _ = 1 := by rw [hggi, Matrix.mul_one, hYX]
  have hZinj : Function.Injective Z.mulVec := fun a b hab => by
    have := congrArg (Matrix.mulVec (Yᴴ * J * g)) hab
    simpa only [Matrix.mulVec_mulVec, hLZ, Matrix.one_mulVec] using this
  have hG : (Zᴴ * P * Z).PosDef := hP.conjTranspose_mul_mul_same hZinj

  obtain ⟨R, hRt, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hG
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  letI := Matrix.invertibleOfIsUnitDet R hRu
  have hBt : (R⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular hRt
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hX'P : (Z * R⁻¹)ᴴ * P * (Z * R⁻¹) = 1 := by
    calc (Z * R⁻¹)ᴴ * P * (Z * R⁻¹) = (R⁻¹)ᴴ * (Zᴴ * P * Z) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((R⁻¹)ᴴ * Rᴴ) * (R * R⁻¹) := by rw [← hR]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRiH, hRi', Matrix.one_mul]
  have hX'J : (Z * R⁻¹)ᴴ * J * (Z * R⁻¹) = 0 := by
    calc (Z * R⁻¹)ᴴ * J * (Z * R⁻¹) = (R⁻¹)ᴴ * (Zᴴ * J * Z) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZJ, Matrix.mul_zero, Matrix.zero_mul]
  have hXP : Xᴴ * P * X = 1 := by rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc, hXY]
  obtain ⟨m, mi, hm1, _, hmJ, hmP, hmX⟩ := exists_mem_K J P X (Z * R⁻¹) hJ hJu hP hPJ
    (by rw [hXP, hX'P]) (by rw [hXX, hX'J])
  have hmiH : miᴴ * mᴴ = 1 := by rw [← conjTranspose_mul, hm1, conjTranspose_one]
  have hinv : ∀ M : Matrix (Fin n) (Fin n) ℂ, mᴴ * M * m = M → miᴴ * M * mi = M := fun M hM => by
    calc miᴴ * M * mi = miᴴ * (mᴴ * M * m) * mi := by rw [hM]
      _ = (miᴴ * mᴴ) * M * (m * mi) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hmiH, hm1, Matrix.one_mul, Matrix.mul_one]
  refine ⟨g * m, mi, ?_, hinv J hmJ, hinv P hmP, ?_, R⁻¹, hBt, ?_⟩
  · calc (g * m)ᴴ * J * (g * m) = mᴴ * (gᴴ * J * g) * m := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hg, hmJ]
  · rw [Matrix.mul_assoc, hm1, Matrix.mul_one]
  · calc g * m * X = g * (m * X) := Matrix.mul_assoc _ _ _
      _ = (g * gi) * X * R⁻¹ := by rw [hmX]; simp only [hZ, Matrix.mul_assoc]
      _ = X * R⁻¹ := by rw [hggi, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WittIwasawa
