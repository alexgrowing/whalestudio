import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagQConjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EntOfMapEqZero

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

open Classical in

def eQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if a j ∈ 𝔭 then 1 else 0

def NormOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧ IsUnit P.det

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem eQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (eQ K 𝔭 k a)ᴴ = eQ K 𝔭 k a := by
  unfold eQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem eQ_mul_diagQ_mul_eQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) i j ∈
      (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  unfold eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with hij hi
  · rw [one_mul, mul_one]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) hi)
  · simp
  · exact zero_mem _

theorem solveOnto_of_norm (hN : NormOnto) : SolveOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, hY, hPY, hW, hWh, hEW, hEP1, hEP2, hdet⟩ := hN K F hK 𝔭 h𝔭 m a ha k hk Y
  have hEh := eQ_conjTranspose (K := K) 𝔭 k a
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a

  have h2 : P * eQ K 𝔭 k a = eQ K 𝔭 k a * P := hEP2.trans hEP1.symm
  have h1 : Pᴴ * eQ K 𝔭 k a = eQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose h2
    rw [conjTranspose_mul, conjTranspose_mul, hEh] at h
    exact h.symm
  have hu : IsUnit (Pᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star

  obtain ⟨Z', hZ'⟩ := exists_solve_quot hK h𝔭 (k := k) (by omega)
    (H := eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) (P := P) (Q := (Pᴴ)⁻¹) (S := W)
    (by simp only [conjTranspose_mul, hEh, hH, Matrix.mul_assoc])
    (fun i j => eQ_mul_diagQ_mul_eQ_mem a i j)
    (fun i j => by rw [Matrix.mul_nonsing_inv _ hu, sub_self]; simp)
    hWh
  refine ⟨Y', P, W, eQ K 𝔭 k a * Z' * eQ K 𝔭 k a, Z₀, hY, hPY, hW, ?_⟩
  have h2' : ∀ X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X * P * eQ K 𝔭 k a = X * eQ K 𝔭 k a * P :=
    fun X => by rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have key : W + Pᴴ * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) + (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * P +
      (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) =
      eQ K 𝔭 k a * (W + Pᴴ * Z' + Z'ᴴ * P + Z'ᴴ * (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) * Z') * eQ K 𝔭 k a := by
    simp only [conjTranspose_mul, hEh, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h2',
      ← h1, hEW] <;> abel
  rw [key, hZ', Matrix.mul_zero, Matrix.zero_mul]

theorem discOnto_of_norm (hU : UDModel) (hN : NormOnto) : DiscOnto :=
  discOnto_of_solve hU (solveOnto_of_norm hN)

end Formalism.L2.SG.Pf.discriminantNormShapes
