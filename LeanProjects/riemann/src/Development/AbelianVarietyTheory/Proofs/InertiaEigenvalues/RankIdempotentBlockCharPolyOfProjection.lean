import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharBlock

open Polynomial Matrix

theorem rank_blockPol_of_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (d : Fin t → K) (hba : b * a = 1) :
    (a * b).rank = t ∧
      blockPol (a * b) (a * Matrix.diagonal d * b) = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  constructor
  · apply le_antisymm
    · exact (Matrix.rank_mul_le_left a b).trans (by simpa using Matrix.rank_le_width a)
    · have h1 : b * (a * b) * a = 1 := by
        rw [← Matrix.mul_assoc b a b, hba, Matrix.one_mul, hba]
      have h2 : (b * (a * b) * a).rank ≤ (a * b).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      rw [h1, Matrix.rank_one] at h2
      simpa using h2
  · unfold blockPol
    have hba' : b.map (C (R := K)) * a.map (C (R := K)) = 1 := by
      rw [← Matrix.map_mul, hba]
      simp
    set D : Matrix (Fin t) (Fin t) K[X] := Matrix.diagonal (fun c => (X : K[X]) - C (d c)) with hD
    have hD' : D = (X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - (Matrix.diagonal d).map (C (R := K)) := by
      ext1 i j
      by_cases h : i = j
      · subst h; simp [hD]
      · simp [hD, h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    have key : (X : K[X]) • (a * b).map (C (R := K)) - (a * Matrix.diagonal d * b).map (C (R := K)) + 1
        - (a * b).map (C (R := K)) = 1 + a.map (C (R := K)) * ((D - 1) * b.map (C (R := K))) := by
      rw [hD', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hba', Matrix.mul_one, add_sub_cancel, hD,
      Matrix.det_diagonal]

theorem rank_blockPol_proj : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  intro K _ n r t e E M d hE hM
  let a : Matrix (Fin n) (Fin t) K :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K (Fin r → K) (Fin t → K))
  let b : Matrix (Fin t) (Fin n) K :=
    LinearMap.toMatrix' (LinearMap.snd K (Fin r → K) (Fin t → K) ∘ₗ e.toLinearMap)
  have ha : ∀ w, a.mulVec w = e.symm (0, w) := by
    intro w
    simp [a, LinearMap.toMatrix'_mulVec]
  have hb : ∀ u, b.mulVec u = (e u).2 := by
    intro u
    simp [b, LinearMap.toMatrix'_mulVec]
  have hba : b * a = 1 := by
    apply Matrix.toLin'.injective
    ext1 w
    ext1
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb,
      LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hE' : E = a * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    rw [← hE, LinearEquiv.symm_apply_apply]
  have hM' : M = a * Matrix.diagonal d * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    apply e.injective
    rw [hM, LinearEquiv.apply_symm_apply]
    congr 1
    funext c
    rw [Matrix.mulVec_diagonal]
  rw [hE', hM']
  exact rank_blockPol_of_factor a b d hba

end GlobalTheory.CharBlock
