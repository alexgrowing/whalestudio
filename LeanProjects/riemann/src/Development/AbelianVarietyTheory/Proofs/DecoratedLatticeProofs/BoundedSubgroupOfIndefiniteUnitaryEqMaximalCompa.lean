import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormEigenvalueLeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
open Matrix

namespace GlobalTheory.BoundedUnitary

theorem norm_eigenvalue_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ)
    (hC : ∀ k : ℕ, ∀ i j, ‖(M ^ k) i j‖ ≤ C) (v : Fin n → ℂ) (hv : v ≠ 0) (μ : ℂ)
    (h : M *ᵥ v = μ • v) : ‖μ‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one ..)

open scoped ComplexOrder in

theorem eq_one_of_posSemidef {n : ℕ} (p q : Matrix (Fin n) (Fin n) ℂ) (hp : p.PosSemidef)
    (hqp : q * p = 1) (C : ℝ) (hC : ∀ k : ℕ, ∀ i j, ‖(p ^ k) i j‖ ≤ C)
    (hC' : ∀ k : ℕ, ∀ i j, ‖(q ^ k) i j‖ ≤ C) : p = 1 := by
  have hH := hp.isHermitian
  have hev : ∀ j, hH.eigenvalues j = 1 := by
    intro j
    set v : Fin n → ℂ := ⇑(hH.eigenvectorBasis j) with hvdef
    have hv : v ≠ 0 := by
      intro h0
      have h1 : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h0 i
      exact hH.eigenvectorBasis.orthonormal.ne_zero j h1
    have h1 : p *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := by
      have := hH.mulVec_eigenvectorBasis j
      rw [hvdef, this]
      ext i
      simp
    have h0 : 0 ≤ hH.eigenvalues j := hp.eigenvalues_nonneg j
    have h2 : v = ((hH.eigenvalues j : ℝ) : ℂ) • (q *ᵥ v) := by
      rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]
    have hne : ((hH.eigenvalues j : ℝ) : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_smul] at h2
      exact hv h2
    have h3 : q *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ)⁻¹ • v := by
      conv_rhs => rw [h2]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    have a1 := norm_eigenvalue_le_one p C hC v hv _ h1
    have a2 := norm_eigenvalue_le_one q C hC' v hv _ h3
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h0] at a2
    rw [Complex.norm_real, Real.norm_of_nonneg h0] at a1
    have hpos : 0 < hH.eigenvalues j := lt_of_le_of_ne h0 (fun h => hne (by rw [← h]; simp))
    exact le_antisymm a1 ((inv_le_one₀ hpos).mp a2)
  have hbasis : ∀ j, p *ᵥ ⇑(hH.eigenvectorBasis j) = ⇑(hH.eigenvectorBasis j) := by
    intro j
    rw [hH.mulVec_eigenvectorBasis j, hev j, one_smul]
  have hU : p * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    have := congrFun (hbasis j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  calc p = p * ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by rw [hU2, mul_one]
    _ = 1 := by rw [← mul_assoc, hU, hU2]

open scoped ComplexOrder in

theorem eq_Kset_of_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (G' : Set (Matrix (Fin n) (Fin n) ℂ)), G' ⊆ Formalism.MainNotions.S.UJset ε → Formalism.REAL.Kset ε ⊆ G' → (∀ a ∈ G', ∀ b ∈ G', a * b ∈ G') → (∀ a ∈ G', a⁻¹ ∈ G') → (∃ C : ℝ, ∀ a ∈ G', ∀ i j, ‖a i j‖ ≤ C) → G' = Formalism.REAL.Kset ε := by
  intro n ε G' hU hK hmul hinv ⟨C, hC⟩
  refine Set.Subset.antisymm (fun a ha => ?_) hK
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJH := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJ
  have hJG : J ∈ G' := hK ⟨by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hJH, hJJ], rfl⟩
  have h1G : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G' := hJJ ▸ hmul _ hJG _ hJG
  have hpow : ∀ b ∈ G', ∀ k : ℕ, b ^ k ∈ G' := by
    intro b hb k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hb
  have hleft : ∀ b ∈ G', (J * bᴴ * J) * b = 1 := by
    intro b hb
    have hb' : bᴴ * J * b = J := hU hb
    calc (J * bᴴ * J) * b = J * (bᴴ * J * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hb', hJJ]
  have hinv_eq : ∀ b ∈ G', b⁻¹ = J * bᴴ * J := fun b hb => Matrix.inv_eq_left_inv (hleft b hb)
  have haH : aᴴ ∈ G' := by
    have : aᴴ = J * a⁻¹ * J := by
      rw [hinv_eq a ha]
      calc aᴴ = (J * J) * aᴴ * (J * J) := by rw [hJJ, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [this]
    exact hmul _ (hmul _ hJG _ (hinv a ha)) _ hJG
  have hpG : aᴴ * a ∈ G' := hmul _ haH _ ha
  have hp1 : aᴴ * a = 1 := by
    refine eq_one_of_posSemidef (aᴴ * a) (aᴴ * a)⁻¹ (Matrix.posSemidef_conjTranspose_mul_self a) ?_ C
      (fun k => hC _ (hpow _ hpG k)) (fun k => hC _ (hpow _ (hinv _ hpG) k))
    rw [hinv_eq _ hpG]
    exact hleft _ hpG
  have hp2 : a * aᴴ = 1 := mul_eq_one_comm.mp hp1
  refine ⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hp1], ?_⟩
  have ha' : aᴴ * J * a = J := hU ha
  calc a * J = a * (aᴴ * J * a) := by rw [ha']
    _ = (a * aᴴ) * J * a := by simp only [mul_assoc]
    _ = J * a := by rw [hp2, one_mul]

end GlobalTheory.BoundedUnitary
