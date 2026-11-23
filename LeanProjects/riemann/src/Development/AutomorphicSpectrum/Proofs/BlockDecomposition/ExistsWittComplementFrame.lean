import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_coords {K : Type} [Field K] {n : ℕ} (S : Submodule K (Fin n → K)) (P : Matrix (Fin n) (Fin n) K)
    (hP : ∀ v, P *ᵥ v ∈ S) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K),
      (∀ w, Z *ᵥ w ∈ S) ∧ Z * C = P ∧ Function.Injective Z.mulVec := by
  classical
  let b := Module.finBasis K S
  let Z : Matrix (Fin n) (Fin (Module.finrank K S)) K := Matrix.of fun i k => (b k : Fin n → K) i
  have hZ : ∀ w, Z *ᵥ w = ((∑ k, w k • b k : S) : Fin n → K) := by
    intro w
    ext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm, Submodule.coe_sum, Finset.sum_apply]
  let L : (Fin n → K) →ₗ[K] S := P.mulVecLin.codRestrict S hP
  let c : (Fin n → K) →ₗ[K] (Fin (Module.finrank K S) → K) := b.equivFun.toLinearMap ∘ₗ L
  refine ⟨_, Z, LinearMap.toMatrix' c, fun w => by rw [hZ]; exact Subtype.property _, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hZ]
    have : (∑ k, c v k • b k : S) = L v := b.sum_equivFun (L v)
    rw [this]
    rfl
  · intro w w' h
    rw [hZ, hZ] at h
    have h' := Subtype.coe_injective h
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h'
    exact b.equivFun.symm.injective h'

theorem exists_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  have hc : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => sigma_sigma hσ _
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := hA ▸ hW.xx
  have hBY : B * Y = 0 := hB ▸ hW.yy
  have hAY : A * Y = 1 := hA ▸ hW.xy
  have hBX : B * X = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hc, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
    rw [hB, h]
  obtain ⟨P, hPd⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAP : A * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hBP : B * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, hBY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBX, hAX,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPY : P * Y = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBY, hAY,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  obtain ⟨m, Z, C, hS, hZC, hinj⟩ := exists_coords
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) P (fun v => by
      refine ⟨?_, ?_⟩
      · simp [Matrix.mulVec_mulVec, hAP]
      · simp [Matrix.mulVec_mulVec, hBP])
  have hAZ : A * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).1
  have hBZ : B * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).2
  have hcan : ∀ {ι : Type} (M M' : Matrix (Fin m) ι E), Z * M = Z * M' → M = M' := by
    intro ι M M' h
    ext i j
    exact congrFun (hinj (a₁ := fun i => M i j) (a₂ := fun i => M' i j)
      (funext fun a => congrFun (congrFun h a) j)) i
  have hPZ : P * Z = Z := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBZ, hAZ,
      Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hCZ : C * Z = 1 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPZ, Matrix.mul_one])
  have hCX : C * X = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPX, Matrix.mul_zero])
  have hCY : C * Y = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPY, Matrix.mul_zero])
  refine ⟨m, Z, Matrix.fromRows B (Matrix.fromRows C A), hA ▸ hAZ, hB ▸ hBZ, ?_, ?_⟩
  · rw [frm, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      hBX, hBZ, hBY, hCX, hAX, hCZ, hCY, hAZ, hAY]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  · rw [frm, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, hZC, hPd]
    abel

end GlobalTheory.CompanionTheory.CFin

end
