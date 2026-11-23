import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedBStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasisStatement

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AlgWtHW
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField Finset

section
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sle_mulVec {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ} (hM : ∀ A, M * Φ A = Φ A * M)
    (lam : Fin n → ℤ) {x : ι → ℂ} (hx : x ∈ Sle Φ lam) : M *ᵥ x ∈ Sle Φ lam := by
  have h : Sle Φ lam ≤ (Sle Φ lam).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨ν, hν, hw⟩
    refine Submodule.subset_span ⟨ν, hν, fun D hD => ?_⟩
    show Φ D *ᵥ (M *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw D hD, Matrix.mulVec_smul]
    rfl
  exact h hx

theorem filter_succ (i : Fin n) : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) =
    insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem not_mem_filter_self (i : Fin n) : i ∉ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
  simp

theorem domLE_antisymm {μ lam : Fin n → ℤ} (h1 : DomLE μ lam) (h2 : DomLE lam μ) : μ = lam := by
  have hs : ∀ k : ℕ, ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), lam i := fun k => le_antisymm (h1.2 k) (h2.2 k)
  funext i
  have h := hs ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i), hs i] at h
  linarith

theorem le_of_domLE_swap {lam : Fin n → ℤ} {i j : Fin n} (hij : i < j)
    (h : DomLE (lam ∘ Equiv.swap i j) lam) : lam j ≤ lam i := by
  have h1 := h.2 ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i)] at h1
  have h2 : ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), (lam ∘ Equiv.swap i j) l =
      ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), lam l := by
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl
    have hli : l ≠ i := fun e => by rw [e] at hl; omega
    have hlj : l ≠ j := fun e => by rw [e] at hl; rw [Fin.lt_def] at hij; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [h2] at h1
  simp only [Function.comp, Equiv.swap_apply_left] at h1
  linarith

end

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem algWeight_space_nontrivial (a : AlgWt L n) : Nontrivial a.W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := a.irr
  exact bot_ne_top (α := Subrepresentation a.ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem beig_of_hwAt {a : AlgWt L n} {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
      (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (v : ι → ℂ),
      Agrees a b P ∧ IsBEig (fun B => evM P (evPt τ B)) v lam := by
  obtain ⟨ι, i1, i2, b, P, hP, v, hv, hB⟩ := h
  exact ⟨ι, i1, i2, b, P, v, hP, hv, hB⟩

theorem domLE_of_agrees {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) {v : ι → ℂ} {lam μ : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P (evPt τ B)) v lam) (hμ : IsWt (fun B => evM P (evPt τ B)) μ) :
    DomLE μ lam := by
  obtain ⟨w, hw0, hw⟩ := hμ
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  refine GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy n ι _ hR μ lam w hw hw0 ?_
  have hspan := GlobalTheory.T.algebraicWeight_span_translates_factor_commutant L n a ι b P hP τ v hv.1 w
  refine (Submodule.span_le.2 ?_) hspan
  rintro x ⟨B, M, hM, rfl⟩
  have e : evM P (evPt τ B) *ᵥ (M *ᵥ v) = M *ᵥ (evM P (evPt τ B) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  rw [e]
  exact sle_mulVec hM lam (GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector n ι _ hR v lam hv B)

theorem isWt_of_beig {ι : Type} [Fintype ι] {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {v : ι → ℂ} {lam : Fin n → ℤ}
    (h : IsBEig Φ v lam) : IsWt Φ lam :=
  ⟨v, h.1, fun D hD => h.2 D (fun i j hij => hD (ne_of_gt hij))⟩

theorem beig_transport {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {b' : Module.Basis ι' ℂ a.W} {P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) (hP' : Agrees a b' P') {v' : ι' → ℂ} {lam : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P' (evPt τ B)) v' lam) :
    IsBEig (fun B => evM P (evPt τ B)) (b.toMatrix b' *ᵥ v') lam := by
  have hC : b'.toMatrix b * b.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' b
  refine ⟨fun h0 => hv.1 ?_, fun B hB => ?_⟩
  · have := congrArg (fun x => b'.toMatrix b *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, hC] using this
  · show evM P (evPt τ B) *ᵥ (b.toMatrix b' *ᵥ v') = _
    rw [GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis L n a ι' b' P' ι b P hP' hP τ B, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hC,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have := hv.2 B hB
    simp only at this
    rw [this, Matrix.mulVec_smul]

theorem hw_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  intro L _ _ _ n a τ
  have hanti : ∀ lam, a.HWAt τ lam → Antitone lam := by
    intro lam h
    obtain ⟨ι, _, _, b, P, v, hP, hv⟩ := beig_of_hwAt h
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hlt
    · rw [e]
    · exact le_of_domLE_swap hlt (domLE_of_agrees hP hv
        (GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ) lam (isWt_of_beig hv) i j))
  refine ⟨?_, hanti⟩
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  haveI := algWeight_space_nontrivial a
  haveI := b.index_nonempty
  obtain ⟨v, lam, hv⟩ := GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ)
  refine ⟨lam, ⟨ι, inferInstance, inferInstance, b, P, hP, v, hv.1, hv.2⟩, fun lam' h' => ?_⟩
  obtain ⟨ι', _, _, b', P', v', hP', hv'⟩ := beig_of_hwAt h'
  have hv'' := beig_transport hP hP' hv'
  exact domLE_antisymm (domLE_of_agrees hP hv (isWt_of_beig hv'')) (domLE_of_agrees hP hv'' (isWt_of_beig hv))

end

end GlobalTheory.AlgWtHW
