import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMapFlag

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem adjugate_last_col_sum_and_det_of_coset (Z Z' P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (v v' : Fin (r + 1) → S.V) (φ : S.V →ₗ[E] S.V) (hZ : Z' = P * Z * Q)
    (hv : ∀ b, v' b = φ (∑ c, Q c b • v c)) (hQ : Q.det = 1) (hP : P.det = 1)
    (hPl : ∀ a, P a (Fin.last r) = if a = Fin.last r then 1 else 0) :
    ∑ b, Z'.adjugate b (Fin.last r) • v' b = φ (∑ b, Z.adjugate b (Fin.last r) • v b) ∧
      Z'.det = Z.det := by
  have hQQ : Q * Q.adjugate = 1 := by rw [Matrix.mul_adjugate, hQ, one_smul]
  have hPP : P.adjugate * P = 1 := by rw [Matrix.adjugate_mul, hP, one_smul]
  have hPl' : ∀ d, P.adjugate d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have := congrFun (congrFun hPP d) (Fin.last r)
    simpa [Matrix.mul_apply, hPl, Matrix.one_apply] using this
  have hW : ∀ c, (Q * (Q.adjugate * (Z.adjugate * P.adjugate))) c (Fin.last r) =
      Z.adjugate c (Fin.last r) := by
    intro c
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_apply]
    simp [hPl']
  refine ⟨?_, ?_⟩
  · rw [hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    simp only [hv, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, ← hW c, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one]

theorem omp_coset (F : FlagG S r T) (F0 : FlagG S r T') (σ γ1 s' : S.V ≃ₗ[E] S.V)
    (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hσ' : σ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hγ2 : σ * γ1 * s' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ j, ∀ x ∈ F.Xa (j + 1), σ.symm x - x ∈ F.Xa j) (hσz : σ.symm F.z - F.z ∈ F.X)
    (hsf : ∀ j, ∀ x ∈ F0.Xa (j + 1), s' x - x ∈ F0.Xa j) (hsz : s' F0.z - F0.z ∈ F0.X) :
    omp F (mapFlag (σ * γ1 * s') hγ2 F0) = σ (omp F (mapFlag γ1 hγ1 F0)) ∧
    (Zhat F (mapFlag (σ * γ1 * s') hγ2 F0)).det = (Zhat F (mapFlag γ1 hγ1 F0)).det ∧
    omp (mapFlag (σ * γ1 * s') hγ2 F0) F = σ (omp (mapFlag γ1 hγ1 F0) F) ∧
    (Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F).det = (Zhat (mapFlag γ1 hγ1 F0) F).det := by
  obtain ⟨M, hM, hMd, hMl⟩ := coef_mat F0 (s' : S.V →ₗ[E] S.V) (fun j x hx => hsf j x hx) hsz
  obtain ⟨N, hN, hNd, hNl⟩ := coef_mat F (σ.symm : S.V →ₗ[E] S.V) (fun j x hx => hσf j x hx) hσz
  have hM' : ∀ b, s' (F0.fvec b) = ∑ c, M c b • F0.fvec c := hM
  have hN' : ∀ b, σ.symm (F.fvec b) = ∑ c, N c b • F.fvec c := hN
  have hs : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσ
  have hv1 : ∀ b, (mapFlag (σ * γ1 * s') hγ2 F0).fvec b =
      σ (∑ c, M c b • (mapFlag γ1 hγ1 F0).fvec c) := by
    intro b
    rw [fvec_mapFlag, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hM' b, map_sum]
    simp only [fvec_mapFlag, map_smul]
  have hv2 : ∀ b, F.fvec b = σ (∑ c, N c b • F.fvec c) := by
    intro b
    rw [← hN', LinearEquiv.apply_symm_apply]
  have hZ1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) = Nᴴ * Zhat F (mapFlag γ1 hγ1 F0) * M := by
    ext a b
    have e1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) a b =
        S.hT (F.fvec a) ((mapFlag (σ * γ1 * s') hγ2 F0).fvec b) := rfl
    rw [e1, hv1 b, hv2 a, hs]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hZ2 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F = Mᴴ * Zhat (mapFlag γ1 hγ1 F0) F * N := by
    ext a b
    have e1 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F a b =
        S.hT ((mapFlag (σ * γ1 * s') hγ2 F0).fvec a) (F.fvec b) := rfl
    rw [e1, hv1 a, hv2 b, hs]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ1 hv1 hMd
    (by simp [Matrix.det_conjTranspose, hNd])
    (by intro a; rw [Matrix.conjTranspose_apply, hNl]; split_ifs <;> simp)
  obtain ⟨h3, h4⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ2 hv2 hNd
    (by simp [Matrix.det_conjTranspose, hMd])
    (by intro a; rw [Matrix.conjTranspose_apply, hMl]; split_ifs <;> simp)
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
