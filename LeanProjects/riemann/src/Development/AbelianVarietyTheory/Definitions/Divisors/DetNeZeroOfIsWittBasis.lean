import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.UG (cT)

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def blockColumnMatrix {R : Type} {k : ℕ} (a b : Matrix (Fin n) (Fin k) R) : Matrix (Fin (n + n)) (Fin k) R :=
  (Matrix.fromRows a b).submatrix finSumFinEquiv.symm id

omit [NumberField E] in

theorem mem_unipN_iff (g : UA σ J₂) : g ∈ unipN σ J₂ ↔ (mat g - 1) * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = 0 := by
  have e : ∀ i j, (mat g * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1) i j =
      mat g i (finSumFinEquiv (.inl j)) + mat g i (finSumFinEquiv (.inr j)) := fun i j => by
    rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    simp [Matrix.one_apply]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, mem_unipOf, mem_siegelOf, keepsDiag_iff]
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    have h3 : ∀ i, mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) = (1 : Matrix (Fin n) (Fin n) (AE F E)) i j :=
      fun i => congrFun (congrFun h2 i) j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> rw [e] <;>
      simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    · exact h3 i
    · exact (h1 i j).trans (h3 i)
  · intro h
    have h3 : ∀ i j, mat g (finSumFinEquiv i) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv i) (finSumFinEquiv (.inr j)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 i j :=
      fun i j => by
        rw [← e, h]
        simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    exact ⟨fun i j => (h3 (.inr i) j).trans (h3 (.inl i) j).symm, Matrix.ext fun i j => h3 (.inl i) j⟩

theorem cocompact_unipN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    LocallyCompactSpace (unipN σ J₂) ∧
      ∃ C : Set (unipN σ J₂), IsCompact C ∧ ∀ g : unipN σ J₂, ∃ γ : ratN σ J₂, γ • g ∈ C := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨δ, hδ, hδs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hc : δ * σ l⁻¹ ≠ 0 := mul_ne_zero hδ ((map_ne_zero σ).2 (inv_ne_zero hl))
  set c := δ * σ l⁻¹ with hcd
  set H : Matrix (Fin n) (Fin n) E := c • J.map σ with hH
  have hHd : H.det ≠ 0 := by
    rw [hH, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ hc) ?_
    rw [show (J.map σ).det = σ J.det from ((σ : E →+* E).map_det J).symm]
    exact (map_ne_zero σ).2 hdet
  have hHh : ∀ i j, σ (H j i) = H i j := fun i j => by
    have h := congrArg σ (hJ i j)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_neg, hσ] at h
    simp only [hH, hcd, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hδs]
    linear_combination (-δ) * h
  have hG : c • J₂.map σ = dblGram finSumFinEquiv H := by
    rw [h₂, dblGram, dblGram, blkMat_map _ _ (map_zero σ), Matrix.map_neg _ (map_neg σ), hH]
    change (c • Matrix.fromBlocks (J.map σ) 0 0 (-J.map σ)).submatrix _ _ = _
    rw [Matrix.fromBlocks_smul, smul_zero, smul_neg, blkMat]
  have hN : IsHermND σ (c • J₂.map σ) := by
    rw [hG]
    refine ⟨fun i j => ?_, ?_⟩
    · obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero,
          Matrix.neg_apply, map_neg, hHh]
    · rw [dblGram, det_blkMat, Matrix.det_neg]
      exact mul_ne_zero hHd (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hHd)
  let C : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix 1 1
  let D : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix H⁻¹ 0
  have hi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hHd)
  have hi' : H⁻¹ * H = 1 := mul_eq_one_comm.1 hi
  have hCJ : cT (σ : E →+* E) C * (c • J₂.map σ) = (Matrix.fromCols H (-H)).submatrix id finSumFinEquiv.symm := by
    have : cT (σ : E →+* E) C = (Matrix.fromCols 1 1).submatrix id finSumFinEquiv.symm := by
      ext i j
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [C, cT, blockColumnMatrix, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
          id, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
          Matrix.one_apply, apply_ite (σ : E →+* E), map_one, map_zero, eq_comm (a := i)]
    rw [this, hG, dblGram, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
    simp
  have xy : cT (σ : E →+* E) C * (c • J₂.map σ) * D = 1 := by
    rw [hCJ]
    simp only [D, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, hi]
    simp
  have xx : cT (σ : E →+* E) C * (c • J₂.map σ) * C = 0 := by
    rw [hCJ]
    simp only [C, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows]
    simp
  have hP : 1 - D * (cT (σ : E →+* E) C * (c • J₂.map σ)) =
      C * ((Matrix.fromCols (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix id finSumFinEquiv.symm :
        Matrix (Fin n) (Fin (n + n)) E) := by
    rw [hCJ]
    simp only [C, D, blockColumnMatrix]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.submatrix_one_equiv finSumFinEquiv.symm,
      ← Matrix.fromBlocks_one]
    ext i j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;> simp [hi']
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • J₂.map σ) C := by
    refine ⟨Matrix.mulVec_injective_iff.1 fun x y h => funext fun i => ?_, xx⟩
    have := congrFun h (finSumFinEquiv (.inl i))
    simpa only [C, blockColumnMatrix, Matrix.submatrix_mulVec_equiv, Matrix.mulVec, Matrix.submatrix_apply, Equiv.symm_apply_apply, id,
      Matrix.fromRows_apply_inl, Matrix.one_apply, dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] using this
  have hCa : GlobalTheory.SiegelSet.adMat F C = blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 := by
    simp only [C, blockColumnMatrix, GlobalTheory.SiegelSet.adMat, ← Matrix.submatrix_map, Matrix.fromRows_map,
      Matrix.map_one _ (map_zero _) (map_one _)]
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ J₂ hc with he
  have hmem : ∀ g : UA σ J₂, g ∈ unipN σ J₂ ↔ e g ∈ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C := fun g => by
    rw [mem_unipN_iff, GlobalTheory.EisCT.mem_unipRad_iff_dual xy, hP, ← hCa]
    refine ⟨fun h => ⟨h, 0, ?_⟩, fun h => h.1⟩
    rw [GlobalTheory.SiegelSet.adMat, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_zero]
    exact (congrArg (· * _) h).trans (Matrix.zero_mul _)
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ _ J₂ c hc
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hcm hN hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hN hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : unipN σ J₂ ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨eH.isClosedEmbedding.locallyCompactSpace, eH ⁻¹' K', eH.isCompact_preimage.2 hK', fun g => ?_⟩
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · show e.symm (γ' : _) ∈ ratU σ J₂
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

theorem existsUnique_isNormN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    ∃! νN : Measure (unipN σ J₂), IsNormN σ νN := by
  obtain ⟨hLC, C, hC, hcov⟩ := cocompact_unipN hcm hl hJ hdet h₂
  obtain ⟨hTG, -, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ J₂
  haveI : BorelSpace (UA σ J₂) := ⟨rfl⟩
  haveI : Countable (ratN σ J₂) := GlobalTheory.UnipMass.countable_ratU' σ J₂ (unipN σ J₂)
  haveI : DiscreteTopology (ratN σ J₂) := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ J₂ (unipN σ J₂)
  obtain ⟨ν, 𝓓, h1, h2, h3⟩ := GlobalTheory.T.cocompact_lattice_unit_covolume _ (ratN σ J₂) C hC hcov
  refine ⟨ν, ⟨h1, 𝓓, h2, h3⟩, ?_⟩
  rintro ν' ⟨h1', 𝓓', h2', h3'⟩
  have e := Measure.isMulLeftInvariant_eq_smul ν' ν
  haveI : MeasurableConstSMul (ratN σ J₂) (unipN σ J₂) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : unipN σ J₂ => (γ : unipN σ J₂) * x).measurable⟩
  haveI : SMulInvariantMeasure (ratN σ J₂) (unipN σ J₂) ν' := ⟨fun γ A _ => measure_preimage_mul ν' (γ : unipN σ J₂) A⟩
  have h4 : IsFundamentalDomain (ratN σ J₂) 𝓓 ν' := h2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h5 : ν' 𝓓 = 1 := (h4.measure_eq h2').trans h3'
  rw [e, Measure.smul_apply, h3, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h5
  rw [e, h5, one_smul]

end GlobalTheory.SWInt

end
