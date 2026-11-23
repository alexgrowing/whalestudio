import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSignsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement

noncomputable section

open Finset Matrix Formalism.REAL

namespace PositivityTheory.RgHe.FrameA

open PositivityTheory.RgHe.Frame PositivityTheory.UnitaryDecomposition

variable {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem hs_nonneg' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hs_emb_sub (a : Matrix (Fin n) (Fin n) ℂ) : hs (emb e a - 1) = hs (a - 1) := by
  have h1 : emb e a - 1 = Matrix.reindex e e (Matrix.fromBlocks (a - 1) 0 0 0) := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [emb, Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  unfold hs
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp [← e.sum_comp, Fintype.sum_sum_type]

theorem emb_mulVec_alt (a : Matrix (Fin n) (Fin n) ℂ) :
    emb e a *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ) = Pi.single (e (Sum.inr ())) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with i | i <;> simp [emb]

theorem frame : PositivityTheory.RgHe.Frame := by
  intro n ε d ε' d' e hF hinj hW
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.interlacing_signature_parity n ε d ε' d' e hF hinj hW
  obtain ⟨ps1, ps2⟩ := GlobalTheory.T.partial_fraction_coefficient_signs d d' hinj
  have hD : ∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i := fun i => by
    have h := ps1 i
    by_cases hi : ε i = true
    · rw [if_pos hi, one_mul]
      rwa [((hs1 i).1 hi).neg_one_pow, one_mul] at h
    · rw [if_neg hi]
      have ho : ¬ Even (above d d' (d i)) := fun h' => hi ((hs1 i).2 h')
      rw [(Nat.not_even_iff_odd.1 ho).neg_one_pow] at h
      linarith
  have hR : ∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j) := fun j => by
    have h := ps2 j
    by_cases hj : ε' j = true
    · rw [if_pos hj]
      rw [(Nat.not_even_iff_odd.1 ((hs2 j).1 hj)).neg_one_pow] at h
      linarith
    · rw [if_neg hj]
      have he : Even (above d d' (d' j)) := by
        by_contra h'
        exact hj ((hs2 j).2 h')
      rw [he.neg_one_pow, one_mul] at h
      linarith
  obtain ⟨g, X, hgU, hXg, hblk, hβ⟩ := GlobalTheory.T.exists_unitary_interlacing_realization n ε d ε' d' e hF.1 hF.2 hinj hD hR
  set J := Jm ε with hJ
  have hJJ : J * J = 1 := Jm_mul_self ε
  have h2 : (J * gᴴ * J) * g = 1 := by
    have : (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [this, hgU, hJJ]
  have hinv : g⁻¹ = J * gᴴ * J := Matrix.inv_eq_left_inv h2
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h2
  have h1 : g * (J * gᴴ * J) = 1 := by rw [← hinv]; exact Matrix.mul_nonsing_inv g hdet
  let gu : UJ ε := ⟨⟨g, J * gᴴ * J, h1, h2⟩, hgU⟩
  have hgu : um gu = g := rfl
  have hgu' : um gu⁻¹ = g⁻¹ := by
    rw [hinv]; rfl
  refine ⟨gu, fun Y => ?_, ?_⟩
  · rw [hgu, hgu']
    exact GlobalTheory.T.trace_diagonal_block_conjugate_formula n e d d' g X hdet hXg hblk Y
  · set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hDd
    have hX : X = g * D * g⁻¹ := by
      rw [hXg.symm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    set v : Fin (n + 1) → ℂ := Pi.single (e (Sum.inr ())) 1 with hv
    have hdi : Function.Injective fun i => ((d i : ℝ) : ℂ) := fun i j h =>
      Sum.inl_injective (hinj (by simpa using h))
    have hcyc : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0 := by
      intro A hA hAv
      rw [hX] at hA
      exact GlobalTheory.T.commutant_annihilating_vector_zero g _ v hdet hdi (fun i => by rw [hinv]; exact hβ i) A hA hAv
    obtain ⟨c, hc, hAc⟩ := GlobalTheory.T.commutator_coercive_on_annihilator X v hcyc
    refine ⟨c * hs g * hs g⁻¹ + 1, by have := hs_nonneg' g; have := hs_nonneg' g⁻¹; positivity, fun h => ?_⟩
    set B := emb e (um h) with hB
    set B' := emb e (um h⁻¹) with hB'
    have hBB : B * B' = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.mul_inv h.1
    have hBB' : B' * B = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.inv_mul h.1
    set δ := dg d - (um gu⁻¹ * B' * um gu) * dg d * (um gu⁻¹ * B * um gu) with hδ
    have hdg : dg d = D := rfl
    have key : (B - 1) * X - X * (B - 1) = B * (g * δ * g⁻¹) := by
      rw [hδ, hgu, hgu', hdg, hX]
      have e1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hdet
      have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      have e3 : B * (g * (g⁻¹ * (B' * (g * (D * (g⁻¹ * (B * (g * g⁻¹)))))))) = g * (D * (g⁻¹ * B)) := by
        rw [e2, Matrix.mul_one, ← Matrix.mul_assoc g g⁻¹, e2, Matrix.one_mul, ← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
      rw [e3]
      abel
    have hAv : (B - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hB, emb_mulVec_alt, sub_self]
    have i1 := hAc (B - 1) hAv
    rw [key] at i1
    have i2 : hs (B * (g * δ * g⁻¹)) ≤ hs B * (hs g * hs δ * hs g⁻¹) := by
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_left ?_ (hs_nonneg' _))
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _) (hs_nonneg' _))
    have i3 : hs (um h - 1) = hs (B - 1) := (hs_emb_sub (e := e) (um h)).symm
    rw [i3]
    have := hs_nonneg' B; have := hs_nonneg' δ; have := hs_nonneg' g; have := hs_nonneg' g⁻¹
    calc hs (B - 1) ≤ c * (hs B * (hs g * hs δ * hs g⁻¹)) := i1.trans (mul_le_mul_of_nonneg_left i2 hc.le)
      _ = (c * hs g * hs g⁻¹) * hs B * hs δ := by ring
      _ ≤ (c * hs g * hs g⁻¹ + 1) * hs B * hs δ := by gcongr; linarith

end PositivityTheory.RgHe.FrameA
