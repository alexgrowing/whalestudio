import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem jacobi_blocks_of_mul {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (M Y : Matrix (α ⊕ β) (α ⊕ β) R) (d : R) (h : M * Y = d • (1 : Matrix (α ⊕ β) (α ⊕ β) R)) :
    M.toBlocks₁₁.det * Y.det = d ^ Fintype.card α * Y.toBlocks₂₂.det := by
  have hY : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Y).symm
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks M).symm
  have h' := h
  rw [hM, hY, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero] at h'
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp h'
  have key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y =
      Matrix.fromBlocks (d • 1) 0 Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    conv_lhs => rw [hY]
    rw [Matrix.fromBlocks_multiply, h11, h12]
    simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hd
  exact hd

theorem genM_det_ne_zero_of_nontrivial (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  have hm : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [RingHom.map_det, hm, Matrix.det_one, map_zero] at h1
  exact one_ne_zero h1

theorem exists_equiv_castLE_rev {n s : ℕ} (hs : s ≤ n) : ∃ e : Fin (n - s) ⊕ Fin s ≃ Fin n,
    (∀ a, e (.inl a) = Fin.castLE (Nat.sub_le n s) a) ∧ ∀ q, e (.inr q) = Fin.rev (Fin.castLE hs q) := by
  refine ⟨(Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans
    (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hs))), ?_, ?_⟩
  · intro a
    ext
    simp
  · intro q
    have hq := q.isLt
    ext
    simp
    omega

theorem jacobi_adjugate_perm {R : Type} [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (h1 : 1 ≤ s)
    (M : Matrix (Fin n) (Fin n) R) (hM : M.det ≠ 0) (σ : Equiv.Perm (Fin n)) : ∃ ε : ℤˣ,
    (Matrix.of fun q p : Fin s => M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det =
      (ε : ℤ) • (M.det ^ (s - 1) * (Matrix.of fun a b : Fin (n - s) =>
        M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det) := by
  obtain ⟨e, he1, he2⟩ := exists_equiv_castLE_rev hs
  obtain ⟨f, hf1, hf2⟩ : ∃ f : Fin (n - s) ⊕ Fin s ≃ Fin n,
      (∀ a, f (.inl a) = σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) ∧ ∀ p, f (.inr p) = σ (Fin.castLE hs p) :=
    ⟨(e.trans Fin.revPerm).trans σ, fun a => by simp [he1], fun p => by simp [he2]⟩
  have hmul : M.submatrix f e * M.adjugate.submatrix e f =
      M.det • (1 : Matrix (Fin (n - s) ⊕ Fin s) (Fin (n - s) ⊕ Fin s) R) := by
    rw [← Matrix.submatrix_mul M M.adjugate f e f e.bijective, Matrix.mul_adjugate]
    ext i j
    simp [Matrix.one_apply]
  have hJ := jacobi_blocks_of_mul _ _ _ hmul
  have hC : (M.submatrix f e).toBlocks₁₁ = Matrix.of fun a b : Fin (n - s) =>
      M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hf1, he1]
  have hT : (M.adjugate.submatrix e f).toBlocks₂₂ = Matrix.of fun q p : Fin s =>
      M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p)) := by
    ext q p
    simp [Matrix.toBlocks₂₂, hf2, he2]
  have hY : (M.adjugate.submatrix e f).det =
      ((Equiv.Perm.sign (e.trans f.symm) : ℤ) : R) * M.det ^ (n - 1) := by
    have hre : M.adjugate.submatrix e f = (M.adjugate.submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j
      simp
    rw [hre, Matrix.det_permute, Matrix.det_submatrix_equiv_self, Matrix.det_adjugate, Fintype.card_fin]
  rw [hC, hT, hY, Fintype.card_fin] at hJ
  have hpow : M.det ^ (n - 1) = M.det ^ (n - s) * M.det ^ (s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hJ
  refine ⟨Equiv.Perm.sign (e.trans f.symm), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (n - s) hM)
  rw [zsmul_eq_mul]
  linear_combination -hJ

theorem cofAct_initMinor : ∀ (R : Type) [CommRing R] [IsDomain R] (n s : ℕ) (hs : s ≤ n), 1 ≤ s → ∀ σ : Equiv.Perm (Fin n), ∃ ε : ℤˣ, cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) = (ε : ℤ) • ((genM R n).det ^ (s - 1) * initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s)) := by
  intro R _ _ n s hs h1 σ
  obtain ⟨ε, hε⟩ := jacobi_adjugate_perm hs h1 (genM R n) (genM_det_ne_zero_of_nontrivial R n) σ
  refine ⟨ε, ?_⟩
  have hlhs : cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) =
      (Matrix.of fun q p : Fin s => (genM R n).adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
    rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext q p
    simp [cofAct]
  have hrhs : (Matrix.of fun a b : Fin (n - s) =>
      genM R n (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det =
      initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s) := by
    rw [initMinor]
    congr 1
  rw [hlhs, hε, hrhs]

end GlobalTheory.ValCmp
