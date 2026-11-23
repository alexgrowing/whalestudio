import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.LocalFromCover

theorem trace_conj {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have h2 := congrArg (fun A => (A * Jm p q).trace) h
  simp only [add_mul, Matrix.trace_add, zero_mul, Matrix.trace_zero] at h2
  rw [mul_assoc, hJ, mul_one, Matrix.trace_mul_comm, ← mul_assoc, hJ, one_mul, Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem trace_reindex' {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) : (Matrix.reindex e e Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun a => Z a a

theorem exp_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • plainMat e Z) = plainMat e (NormedSpace.exp (t • Z)) := by
  have h : t • plainMat e Z = Matrix.reindex e e (t • Z) := by
    ext a b; simp [plainMat]
  rw [h]
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) (t • Z)).symm

theorem exp_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • barMat e Z) = barMat e (NormedSpace.exp (t • Z)) := by
  have h0 : ∀ A : Mat p q, A.map (starRingEnd ℂ) = Aᴴᵀ := fun A => by ext a b; simp
  have h1 := exp_plainMat e (Z.map (starRingEnd ℂ)) t
  have h2 : t • Z.map (starRingEnd ℂ) = (t • Z)ᴴᵀ := by ext a b; simp
  rw [h2, Matrix.exp_transpose, Matrix.exp_conjTranspose, ← h0] at h1
  exact h1

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem fr_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.fr τ * toFrame M τ Y * (M.fr τ)⁻¹ = Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ hd, mul_one]

theorem trace_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (toFrame M τ Y).trace = Y.trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]

theorem rep_exp (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • toFrame M τ Y)) = M.σ τ (NormedSpace.exp (t • Y)) := by
  rw [DSModel.rep, ← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul, fr_toFrame]

variable {M τ}

theorem matches_exp {p q : ℕ} {T : GrpData p q} {R : DSRep T}
    {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ} {m : ℤ} {U : M.H τ → R.U.H} (h : Matches R M τ φ m U)
    (hφ : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z)))
    {Z : Mat p q} (hZ : Z ∈ upq p q) (t : ℝ) (x : M.H τ) :
    U (M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x) =
      ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m • R.U.π (T.expt (t • Z)) (U x) := by
  rw [rep_exp, hφ, h.grp, T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), smul_smul,
    ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]

theorem hasDerivAt_sq_zpow {p q : ℕ} (T : GrpData p q) (m : ℤ) {Z : Mat p q} (hZ : Z ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m) (m * (Z.trace / 2)) 0 := by
  have h3 := (hasDerivAt_zpow m _ (.inl (Units.ne_zero _))).comp (0 : ℝ)
    (GlobalTheory.RealPar.Cover.hasDerivAt_sq (T := T) hZ)
  refine h3.congr_deriv ?_
  simp [T.expt_zero]

theorem exists_locIt (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hN : Nontrivial R₂.HK.V) (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (hB : IsCoverIt R₁ R₂ B) :
    ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  let A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ :=
    LinearMap.mk₂ ℂ (fun P y => U.symm (B (κ P) (U' y)))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [LinearIsometryEquiv.map_smulₛₗ, LinearMap.map_smulₛₗ])
  have hA : ∀ P y, A P y = U.symm (B (κ P) (U' y)) := fun _ _ => rfl
  have hmC : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  refine ⟨A, fun P y => ?_, ?_, fun P w => ?_, ?_, ?_⟩
  · refine Submodule.subset_span (h₁.smooth _ ?_)
    rw [hA, U.apply_symm_apply]
    exact hB.kfin _ _
  · obtain ⟨v, hv⟩ := exists_ne (0 : R₂.HK.V)
    obtain ⟨P, hP⟩ := hB.ne (R₂.ι v) fun h0 => hv (R₂.ι_inj (by rw [h0, map_zero]))
    refine ⟨κ.symm P, U'.symm (R₂.ι v), Submodule.subset_span (h₂.smooth _ ?_), ?_⟩
    · rw [U'.apply_symm_apply]; exact ⟨v, rfl⟩
    · rw [hA, U'.apply_symm_apply, κ.apply_symm_apply]
      intro h0
      exact hP (U.symm.injective (by rw [h0, map_zero]))
  · haveI : CompleteSpace (M'.H τ) := U'.toIsometryEquiv.completeSpace
    obtain ⟨c, hc⟩ := hB.bdd (κ P)
    let L : M'.H τ →L[ℂ] M.H τ := (A P).mkContinuous c fun y => by
      rw [hA, U.symm.norm_map, ← U'.norm_map y]; exact hc _
    refine ⟨(InnerProductSpace.toDual ℂ (M'.H τ)).symm ((innerSL ℂ w).comp L), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · intro X hX P y
    rw [← h₁.lie] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    have h1 := (hasDerivAt_sq_zpow T₁ m hZ).fun_smul (hB.src Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h3 : (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by ext a b; simp [barMat]
    have h4 : (barMat e Z).trace = -Z.trace := by
      rw [barMat, trace_reindex', ← trace_conj hZ]
      simp [Matrix.trace]
    convert h2 using 1
    · funext t
      apply U.injective
      rw [matches_exp h₁ (exp_barMat e) hZ, hA]
      simp
    · rw [hA, fr_toFrame, trace_toFrame, h3, h4, map_sub, map_smul, hκ.1, hmC,
        show 2 * (aT : ℂ) * (Z.trace / 2) = aT * Z.trace by ring]
      simp [T₁.expt_zero]
  · intro Y hY P y
    rw [← h₂.lie] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    have h1 := (hasDerivAt_sq_zpow T₂ m' hZ).star.fun_smul (hB.tgt Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h4 : (plainMat e' Z).trace = Z.trace := trace_reindex' e' Z
    have h5 : star ((m' : ℂ) * (Z.trace / 2)) = -((aS : ℂ) * Z.trace) := by
      rw [Complex.star_def, map_mul, map_intCast, map_div₀, trace_conj hZ, map_ofNat, hmC']
      ring
    convert h2 using 1
    · funext t
      rw [hA, matches_exp h₂ (exp_plainMat e') hZ, LinearMap.map_smulₛₗ]
      rfl
    · rw [h5, hA, fr_toFrame, trace_toFrame, h4, map_add, map_smul, plainMat, hκ.2]
      simp [T₂.expt_zero]
      abel

end GlobalTheory.Chain.RealIt.LocalFromCover

end
