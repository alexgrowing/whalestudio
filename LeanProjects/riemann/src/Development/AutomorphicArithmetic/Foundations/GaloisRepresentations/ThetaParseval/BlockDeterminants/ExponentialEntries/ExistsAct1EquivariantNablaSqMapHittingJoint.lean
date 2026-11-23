import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub

open MvPolynomial Formalism.BasicNotions UpperTheory.TP.RP

namespace UpperTheory.TP.RP

private noncomputable def sAlg {n d : ℕ} (h : n ≤ d) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] PP n d :=
  aeval fun v => xv v.1 (Fin.castLE h v.2)

private theorem sAlg_rowAct {n d : ℕ} (h : n ≤ d) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    sAlg h (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g.transpose f) = leftSub g (sAlg h f) := by
  have key : (sAlg h).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g.transpose) = (leftSub g).comp (sAlg h) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [sAlg, Formalism.GradedWeylDivisibility.rowAct, leftSub, xv, Matrix.transpose_apply, map_sum, aeval_X, MvPolynomial.algebraMap_eq]
  exact congrArg (fun φ => φ f) key

private theorem rowAct_lp {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g.transpose (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl) =
      C g.det * Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det]
  have hM : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g.transpose).mapMatrix
      (Matrix.of fun p q : Fin n => (X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) : MvPolynomial (Fin n × Fin n) ℂ)) =
      (g.map C).transpose * Matrix.of fun p q : Fin n => (X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) : MvPolynomial (Fin n × Fin n) ℂ) := by
    ext p q
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply, aeval_X, Matrix.transpose_apply, MvPolynomial.algebraMap_eq]
  rw [hM, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) g).symm

private theorem sAlg_lp {n d : ℕ} (h : n ≤ d) (k : ℕ) (hk : k ≤ n) :
    sAlg h (Formalism.GradedWeylDivisibility.lpMinor ℂ k hk hk) = ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ k (hk.trans h) hk) := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [sAlg, ofTall, xv, aeval_X, rename_X, Matrix.transpose_apply, Fin.castLE_castLE]

private theorem key_succ {m d : ℕ} (h : m + 1 ≤ d) (ν μ : Fin (m + 1) → ℕ) (t : ℕ)
    (hν : ∀ k, μ k = ν k + t) (hl : ν (Fin.last m) = 0) :
    sAlg h (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) * sAlg h (Formalism.GradedWeylDivisibility.lpMinor ℂ (m + 1) le_rfl le_rfl) ^ t = joint h μ := by
  have h1 : ∀ ρ : Fin (m + 1) → ℕ, sAlg h (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ρ) = ofTall (Formalism.GradedWeylDivisibility.hw ℂ h ρ) := by
    intro ρ
    simp only [Formalism.GradedWeylDivisibility.hw, map_prod, map_pow]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [sAlg_lp]
  rw [h1, sAlg_lp, ← map_pow, ← map_mul]
  unfold joint
  congr 1
  simp only [Formalism.GradedWeylDivisibility.hw]
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have e1 : ∀ i : Fin m, μ (Fin.castSucc i) - Formalism.GradedWeylDivisibility.nuNext μ (Fin.castSucc i) =
      ν (Fin.castSucc i) - Formalism.GradedWeylDivisibility.nuNext ν (Fin.castSucc i) := by
    intro i
    have hi : (Fin.castSucc i : ℕ) + 1 < m + 1 := by simp
    simp only [Formalism.GradedWeylDivisibility.nuNext, dif_pos hi, hν]
    omega
  have e2 : Formalism.GradedWeylDivisibility.nuNext μ (Fin.last m) = 0 := by simp [Formalism.GradedWeylDivisibility.nuNext]
  have e3 : Formalism.GradedWeylDivisibility.nuNext ν (Fin.last m) = 0 := by simp [Formalism.GradedWeylDivisibility.nuNext]
  simp only [e1, e2, e3, hl, Nat.sub_zero, pow_zero, mul_one]
  rw [hν, hl, zero_add]
  simp

private theorem main_gen {n d : ℕ} (h : n ≤ d) (lam : DomWeight n) (c : ℤ) (μ : Fin n → ℕ) (t : ℕ)
    (ht : ∀ g : GL (Fin n) ℂ, detPow ℂ n g lam.detShift = detPow ℂ n g c * g.1.det ^ t)
    (hj : sAlg h (Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW) * sAlg h (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl) ^ t = joint h μ) :
    ∃ i : nablaSq ℂ n lam →ₗ[ℂ] PP n d, (∀ g x, i (GlobalTheory.Branching.sqRep ℂ n lam g x) = act1 c g (i x)) ∧ ∃ x₀, i x₀ = joint h μ := by
  set s := sAlg h (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl) with hs
  refine ⟨((LinearMap.mulRight ℂ (s ^ t)).comp (sAlg h).toLinearMap).comp (nablaSq ℂ n lam).subtype, ?_, ?_⟩
  · intro g x
    have hx : ((GlobalTheory.Branching.sqRep ℂ n lam g x : nablaSq ℂ n lam) : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n g lam.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose x := rfl
    have hsg : leftSub (g : Matrix (Fin n) (Fin n) ℂ) s = C (g : Matrix (Fin n) (Fin n) ℂ).det * s := by
      rw [hs, ← sAlg_rowAct, rowAct_lp, map_mul]
      simp [sAlg, MvPolynomial.algebraMap_eq]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulRight_apply,
      AlgHom.toLinearMap_apply, hx, act1, LinearMap.smul_apply]
    rw [map_smul, sAlg_rowAct, ht g, map_mul, map_pow, hsg]
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_pow]
    ring
  · have hanti : Antitone lam.natW := by
      intro a b hab
      have := lam.anti hab
      unfold DomWeight.natW
      exact Int.toNat_le_toNat (by omega)
    refine ⟨⟨Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ hanti⟩, ?_⟩
    simpa using hj

end UpperTheory.TP.RP

theorem UpperTheory.TP.RP.exists_act1_equivariant_nablaSq_map_hitting_joint :
    ∀ {n d : ℕ} (h : n ≤ d) (lam : DomWeight n) (c : ℤ) (μ : Fin n → ℕ), (∀ k, (μ k : ℤ) + c = lam.w k) →
      ∃ i : nablaSq ℂ n lam →ₗ[ℂ] PP n d, (∀ g x, i (GlobalTheory.Branching.sqRep ℂ n lam g x) = act1 c g (i x)) ∧ ∃ x₀, i x₀ = joint h μ := by
  intro n d h lam c μ hμ
  cases n with
  | zero =>
    refine main_gen h lam c μ 0 ?_ ?_
    · intro g
      have hg : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      simp [detPow, DomWeight.detShift, hg]
    · simp [Formalism.GradedWeylDivisibility.hw, joint]
  | succ m =>
    have hd : lam.detShift = lam.w (Fin.last m) := by
      unfold DomWeight.detShift
      rw [dif_pos (by omega)]
      congr 1
    have hk : ∀ k, ((lam.natW k : ℕ) : ℤ) = (μ k : ℤ) - μ (Fin.last m) := by
      intro k
      have hle := lam.anti (Fin.le_last k)
      rw [← hμ k, ← hμ (Fin.last m)] at hle
      unfold DomWeight.natW
      rw [hd, ← hμ k, ← hμ (Fin.last m), Int.toNat_of_nonneg (by omega)]
      ring
    refine main_gen h lam c μ (μ (Fin.last m)) ?_ ?_
    · intro g
      have hs : lam.detShift = c + ((μ (Fin.last m) : ℕ) : ℤ) := by
        rw [hd, ← hμ (Fin.last m)]
        ring
      simp only [detPow, hs, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
        Matrix.GeneralLinearGroup.val_det_apply]
    · apply key_succ h
      · intro k
        have := hk k
        omega
      · have := hk (Fin.last m)
        omega
