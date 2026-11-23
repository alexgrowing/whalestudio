import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantBlockDetNormEqPowOfMemSpectrum
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSquareSubmatrixDetNeZeroOfLeftInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusPowEigenvectorMemFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private noncomputable def filS {l : ℕ} [Fact l.Prime] (K : FinExt l) : Subring (Bcr l) where
  carrier := {x | ∀ k : ℕ, (PP l).ιB (((PP l).φB ^ k) x) ∈ ((PP l).PD K).Fil 0}
  mul_mem' := fun {a b} ha hb k => by
    rw [map_mul, map_mul]
    simpa using ((PP l).PD K).Fil_mul 0 0 _ _ (ha k) (hb k)
  one_mem' := fun k => by
    rw [map_one, map_one]; exact ((PP l).PD K).one_mem
  add_mem' := fun {a b} ha hb k => by
    rw [map_add, map_add]; exact Submodule.add_mem _ (ha k) (hb k)
  zero_mem' := fun k => by
    rw [map_zero, map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha k => by
    rw [map_neg, map_neg]; exact Submodule.neg_mem _ (ha k)

private theorem frobenius_iterate_unramified {l : ℕ} [Fact l.Prime] (K : FinExt l) (k : ℕ) (c : ↥(K0 K)) :
    ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K,
      ((PP l).PD K).φ_K₀]

private theorem K0_mem {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(K0 K)) :
    algebraMap ↥(K0 K) (Bcr l) c ∈ filS K := by
  intro k
  rw [AlgHom.coe_pow, frobenius_iterate_unramified, ← (PP l).PD_ι K, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul ↥K.1]
  exact Submodule.smul_mem _ _ ((PP l).PD K).one_mem

private theorem fil_iff {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (x : Bdr l) :
    x ∈ ((PP l).PD K).Fil 0 ↔ x ∈ ((PP l).PD K').Fil 0 := by
  obtain ⟨T⟩ := tiedP l
  rw [T.fil, T.fil]

theorem UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K)), M' * M = 1 → (∀ (k : ℕ) i j, (PP l).ιB (((PP l).φB)^[k] (M i j)) ∈ ((PP l).PD (botExt l)).Fil 0) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖a‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' F hM hFil hφ a ha
  obtain ⟨T⟩ := tiedP l
  haveI : IsDomain (Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hdet⟩ := UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum (K0 K) F a ha
  set j : ↥(K0 K) →+* Bcr l := algebraMap ↥(K0 K) (Bcr l) with hj
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin d) (Fin r) (Bcr l), X = M * Y.map j := ⟨_, rfl⟩
  have hZX : (Z.map j * M') * X = 1 := by
    rw [hXd]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M', hM, Matrix.one_mul, ← Matrix.map_mul, hZY,
      Matrix.map_one _ (map_zero j) (map_one j)]
  have hYψ : (Y.map j).map ψ = Y.map j := by
    ext i k
    simp only [Matrix.map_apply]
    rw [hψ, hj, frobenius_iterate_unramified, hσ]
  have hX : X.map ψ = X * F'.map j := by
    rw [hXd]
    rw [Matrix.map_mul, hYψ, hψ, hφ, Matrix.mul_assoc, ← Matrix.map_mul, hFY, Matrix.map_mul,
      Matrix.mul_assoc]
  obtain ⟨s, hs⟩ := UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse X _ hZX
  have hXS : ∀ i k, X i k ∈ filS K := by
    intro i k
    simp only [hXd, Matrix.mul_apply, Matrix.map_apply]
    refine Subring.sum_mem _ fun c _ => Subring.mul_mem _ (fun n => ?_) (K0_mem K _)
    rw [AlgHom.coe_pow]
    exact (fil_iff _ _ _).1 (hFil n i c)
  have hbS : (X.submatrix s id).det ∈ filS K := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hXS _ _)
  have hb : ((PP l).φB)^[f] (X.submatrix s id).det = j F'.det * (X.submatrix s id).det := by
    have h1 : (X.submatrix s id).map ψ = X.submatrix s id * F'.map j := by
      ext i k
      have := congrFun (congrFun hX (s i)) k
      simpa [Matrix.mul_apply] using this
    rw [← hψ, RingHom.map_det, RingHom.mapMatrix_apply, h1, Matrix.det_mul, mul_comm,
      RingHom.map_det, RingHom.mapMatrix_apply]
  have hle := UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero K f hf hσ _ F'.det hs hb fun i => by
    have := hbS i
    rw [AlgHom.coe_pow] at this
    exact (fil_iff _ _ _).1 this
  rw [hdet] at hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg a) hr.ne').1 hle
