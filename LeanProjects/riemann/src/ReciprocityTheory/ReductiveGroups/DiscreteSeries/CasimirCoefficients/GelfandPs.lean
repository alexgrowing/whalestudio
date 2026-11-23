import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPsB

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private lemma conj_single_lemma (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single a b (1 : ℂ) * B =
      ∑ c, ∑ d, (Aᵀ a c * Bᵀ d b) • Matrix.single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, ite_mul, mul_ite,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private lemma mul_single_rev_mul_eq_sum (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) * B =
      ∑ c, ∑ d, (B.submatrix Fin.rev Fin.rev a c * A.submatrix Fin.rev Fin.rev d b) •
        Matrix.single (Fin.rev d) (Fin.rev c) (1 : ℂ) := by
  rw [conj_single_lemma, Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun d => ?_
  refine Fintype.sum_equiv Fin.revPerm _ _ fun c => ?_
  simp [mul_comm]

private lemma toMK_inv_mul_and_mul_inv (g : KG ε) : toMK g⁻¹ * toMK g = 1 ∧ toMK g * toMK g⁻¹ = 1 := by
  have hg : toMK g ∈ Kset ε := g.2
  simp only [Kset, Set.mem_setOf_eq] at hg
  rw [Ps1.toMK_inv_eq]
  refine ⟨?_, ?_⟩
  · first
      | simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hg.1
      | simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hg.1
  · first
      | simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hg.1
      | simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hg.1

private lemma submatrix_rev_mul_eq_one_of_mul_eq_one (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) :
    M.submatrix Fin.rev Fin.rev * N.submatrix Fin.rev Fin.rev = 1 := by
  have e := Matrix.submatrix_mul_equiv M N (Fin.revPerm : Fin n → Fin n) Fin.revPerm
    (Fin.revPerm : Fin n → Fin n)
  rw [h, Matrix.submatrix_one_equiv] at e
  first
    | exact e
    | simpa [Fin.revPerm] using e

theorem gelfand_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ k : ℕ,
        opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (psM T μ) z =
            ((-1 : ℂ) ^ k * gval (icShift lam) k) • psM T μ z ∧
          opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (psM T μ) z =
            gval (icShift (-lam)) k • psM T μ z := by
  haveI := compactSpace_KG ε
  obtain ⟨U₀, hU₀o, hpos, -, hdiff, -⟩ := psM_holo T μ
  refine ⟨U₀ ∩ Ps1.Uset ε, hU₀o.inter Ps1.isOpen_Uset,
    fun z hz => ⟨hpos hz, Ps1.posSet_subset_Uset hz⟩, hdiff.mono Set.inter_subset_left,
    fun z hz k => ⟨?_, ?_⟩⟩
  · refine GPs.gelfand_Fint T μ _ k _ (fun g y hy => ?_) hz.2
    have hAB : toMK g⁻¹ * toMK g = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).1
    have hBA : toMK g * toMK g⁻¹ = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).2
    rw [GPs.gelfand_conj isOpen_omega _ (toMK g⁻¹) (toMK g) hAB hBA (toMK g⁻¹)ᵀ (toMK g)ᵀ
      (fun a b => conj_single_lemma _ _ a b)
      (by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one])
      (by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]) (phiM_contDiffOn μ) k hy]
    exact (gelfand_phiM μ lam hμ k hy).1
  · refine GPs.gelfand_Fint T μ _ k _ (fun g y hy => ?_) hz.2
    have hAB : toMK g⁻¹ * toMK g = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).1
    have hBA : toMK g * toMK g⁻¹ = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).2
    rw [GPs.gelfand_conj isOpen_omega _ (toMK g⁻¹) (toMK g) hAB hBA
      ((toMK g).submatrix Fin.rev Fin.rev) ((toMK g⁻¹).submatrix Fin.rev Fin.rev)
      (fun a b => mul_single_rev_mul_eq_sum _ _ a b)
      (submatrix_rev_mul_eq_one_of_mul_eq_one _ _ hBA) (submatrix_rev_mul_eq_one_of_mul_eq_one _ _ hAB) (phiM_contDiffOn μ) k hy]
    exact (gelfand_phiM μ lam hμ k hy).2

end ReciprocityTheory.ChartRestriction.DS.S7
