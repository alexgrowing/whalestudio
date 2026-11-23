import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomialsStatement

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHowe.Contraction

open MvPolynomial ReciprocityTheory.PGsh

theorem mem_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  have h : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [h, Matrix.mul_one]

theorem map_star_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext i j; simp

theorem map_star_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  ext i j
  have := congrArg star (congrFun (congrFun hg i) j)
  simp only [Matrix.mul_apply, star_sum, star_mul', Matrix.conjTranspose_apply, Matrix.map_apply] at this ⊢
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem inv_transpose {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    (g⁻¹)ᵀ = g.map star := by
  rw [Matrix.inv_eq_left_inv ((mem_iff g).1 hg)]
  ext i j; simp

theorem det_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).det = star g.det := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
  rfl

theorem star_det {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    star g.det = g.det⁻¹ := by
  have := congrArg Matrix.det ((mem_iff g).1 hg)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem conjTranspose_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    gᴴ ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hg

variable {N n : ℕ}

theorem fischer_swap (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (rename Prod.swap P) (rename Prod.swap Q) = fischer P Q := by
  classical
  have hinj : Function.Injective (Prod.swap : Fin N × Fin n → Fin n × Fin N) := Prod.swap_injective
  rw [fischer_eq_sum _ _ _ subset_rfl, fischer_eq_sum P Q _ subset_rfl,
    support_rename_of_injective hinj, Finset.sum_image
      (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj]
  congr 1
  unfold fw
  rw [Finsupp.prod_mapDomain_index_inj hinj]

theorem subst2_row (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, rowSubst_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

theorem subst2_col (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    rename Prod.swap (subst2 1 g P) = rowSubst g (rename Prod.swap P) := by
  have key : (rename Prod.swap).comp (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g) =
      (rowSubst g).comp (rename Prod.swap) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, rowSubst_X,
      Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  exact congrArg (fun f => f P) key

theorem fischer_subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) Q = fischer P (subst2 hᴴ gᴴ Q) := by
  have h1 : subst2 h g P = subst2 h 1 (subst2 1 g P) := by rw [subst2_mul]; simp
  have h2 : subst2 hᴴ gᴴ Q = subst2 1 gᴴ (subst2 hᴴ 1 Q) := by rw [subst2_mul]; simp
  rw [h1, h2, subst2_row, fischer_rowSubst, ← subst2_row, ← fischer_swap, subst2_col,
    fischer_rowSubst, ← subst2_col, fischer_swap]

theorem fischer_subst2_unitary {h : Matrix (Fin N) (Fin N) ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hh : h ∈ UJset (allPos N)) (hg : g ∈ UJset (allPos n)) (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) (subst2 h g Q) = fischer P Q := by
  rw [fischer_subst2, subst2_mul, (mem_iff h).1 hh, (mem_iff g).1 hg, subst2_one]

theorem exists_contraction {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {H' E : Type} [AddCommGroup H'] [Module ℂ H'] [AddCommGroup E] [Module ℂ E]
    (J : H' →ₛₗ[starRingEnd ℂ] E) (Ψ : E →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ) :
    ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H,
      ∀ P v u, inner ℂ u (I P v) = fischer P (Ψ (J v) u) := by
  let b := stdOrthonormalBasis ℂ H
  refine ⟨LinearMap.mk₂ ℂ (fun P v => ∑ i, fischer P (Ψ (J v) (b i)) • b i) ?_ ?_ ?_ ?_, ?_⟩
  · intro P P' v
    simp only [fischer_add_left, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [fischer_smul_left, Finset.smul_sum, smul_smul]
  · intro P v v'
    simp only [map_add, LinearMap.add_apply, fischer_add_right, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, fischer_smul_right, Finset.smul_sum,
      smul_smul, Complex.conj_conj, RingHom.id_apply]
  · intro P v u
    conv_rhs => rw [← b.sum_repr' u]
    simp only [LinearMap.mk₂_apply, inner_sum, inner_smul_right, map_sum, map_smul, fischer_sum_right,
      fischer_smul_right, inner_conj_symm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompactHowe.Contraction

namespace GlobalTheory.CompactHowe

open Contraction ReciprocityTheory.PGsh

theorem exists_local_contraction : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed n Λ x₃ H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed N Λ' (-x₁) H' σ' hσ' hK'
  have e1 : (fun a => ((x₃ : ℤ) : ℝ) - Λ (Fin.rev a)) = fun a => (ν (Fin.castLE hn a) : ℝ) := by
    funext a; rw [hΛ, Fin.rev_rev]; ring
  have e2 : (fun b => ((-x₁ : ℤ) : ℝ) - Λ' (Fin.rev b)) = fun b => (ν b : ℝ) := by
    funext b; rw [hΛ', Fin.rev_rev]; push_cast; ring
  rw [e1] at hτK
  rw [e2] at hτK'
  obtain ⟨E, i1, i2, i3, π, J, hJ, hπ, hπK, hπJ⟩ := GlobalTheory.T.exists_conjugate_unitaryKType_sameWeight N _ H' _ hτ' hτK'
  obtain ⟨Ψ, hΨ0, hΨ⟩ := GlobalTheory.T.exists_tensor_types_intertwiner_matrix_polynomials N n hn ν H _ E π hν hν0 hτ hτK hπ hπK
  obtain ⟨I, hI⟩ := exists_contraction J Ψ
  refine ⟨I, fun h0 => hΨ0 ?_, fun h hh g hg P v => ?_⟩
  · ext1 w
    ext1 u
    obtain ⟨v, rfl⟩ := hJ.2 w
    by_contra hne
    apply fischer_self_ne_zero _ hne
    rw [← hI, h0]
    simp
  · refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ g u = w := by
      refine ⟨σ gᴴ w, ?_⟩
      have := hσ.1.2 g hg _ (conjTranspose_mem hg)
      rw [mul_eq_one_comm.1 ((mem_iff g).1 hg), hσ.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have hiso : inner ℂ (σ g u) (σ g (I P v)) = inner ℂ u (I P v) :=
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map u (I P v)
    rw [hiso, hI, hI, inv_transpose hg, fischer_smul_left,
      ← fischer_subst2_unitary hh (map_star_mem hg) P, ← hΨ h hh _ (map_star_mem hg), hπJ]
    simp only [map_star_map_star, det_map_star, ContinuousLinearMap.smul_apply, LinearMap.map_smulₛₗ,
      map_smul, LinearMap.smul_apply, fischer_smul_right, RingHom.id_apply, Complex.conj_conj,
      map_zpow₀, starRingEnd_apply, star_star]
    rw [star_det hh, _root_.inv_zpow', neg_neg]
    ring

end GlobalTheory.CompactHowe

end
