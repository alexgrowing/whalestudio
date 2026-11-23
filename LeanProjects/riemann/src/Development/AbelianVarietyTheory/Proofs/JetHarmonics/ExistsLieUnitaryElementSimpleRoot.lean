import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnipotentElement

open Formalism.HermitianLatticeCounting.ExpansionTerms

theorem exp_of_cube_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A * A * A = 0) (t : ℂ) :
    NormedSpace.exp (t • A) = 1 + t • A + (t ^ 2 / 2) • (A * A) := by
  have h3 : A ^ 3 = 0 := by rw [pow_three']; exact h
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_pow, smul_smul, pow_two A]
    simp [Nat.factorial, div_eq_inv_mul]
  · intro b hb
    have hb3 : 3 ≤ b := by simpa using hb
    rw [smul_pow, pow_eq_zero_of_le hb3 h3, smul_zero, smul_zero]

theorem ymat_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (e v : Fin n → ℂ) :
    rankTwoSkewMatrix H e v = vecMulVec e (star v) * H - vecMulVec v (star e) * H := by
  ext i j
  simp [rankTwoSkewMatrix, Formalism.QuantumDeterminants.herm, Matrix.mul_apply, vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

theorem ymat_skew {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (e v : Fin n → ℂ) :
    (rankTwoSkewMatrix H e v)ᴴ * H + H * rankTwoSkewMatrix H e v = 0 := by
  rw [ymat_eq, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH, conjTranspose_vecMulVec,
    conjTranspose_vecMulVec, star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_assoc]
  abel

theorem form_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (x y : EuclideanSpace ℂ (Fin n)) :
    majorantHermitianForm (Matrix.toEuclideanLin H) x y = Formalism.QuantumDeterminants.herm H x.ofLp y.ofLp := by
  unfold majorantHermitianForm Formalism.QuantumDeterminants.herm
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  show star (H *ᵥ y.ofLp) ⬝ᵥ x.ofLp = _
  rw [star_mulVec, hH, dotProduct_mulVec]

theorem isTheta {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) :
    IsSelfAdjointInvolution (Matrix.toEuclideanLin H) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · apply WithLp.ofLp_injective
    show H *ᵥ (H *ᵥ x.ofLp) = x.ofLp
    rw [mulVec_mulVec, hHH, one_mulVec]
  · exact (Matrix.isSymmetric_toEuclideanLin_iff.2 hH) x y

theorem ymat_hs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (e v : EuclideanSpace ℂ (Fin n)) :
    ∑ i, ∑ j, ‖rankTwoSkewMatrix H e.ofLp v.ofLp i j‖ ^ 2 ≤ 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound _ _ (isTheta H hH hHH) n (EuclideanSpace.basisFun (Fin n) ℂ) e v
  refine le_of_eq_of_le ?_ h
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [form_eq H hH, form_eq H hH, EuclideanSpace.basisFun_inner]
  simp [rankTwoSkewMatrix]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem exists_element : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, ∀ a : Fin r, ∃ X : Mx k r, PI.UpqRep.InLieHpk k r X ∧ (∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ 4 * lenA k r z g a.castSucc ^ 2) ∧ ∀ t : ℝ, ∃ m ∈ Formalism.QuantumDeterminants.Nset k r, g * NormedSpace.exp ((t : ℂ) • X) = m * g ∧ Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m = Complex.exp (-(2 * (lenA k r z g a.succ : ℂ) * (t : ℂ)) * Complex.I) := by
  intro k r z hz hT g hg a
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := GlobalTheory.TensLen.isUnit_det_of_unitary hHH hg
  have hHu : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := Matrix.isUnit_det_of_left_inverse hHH
  have hpos := (GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1 a.succ
  obtain ⟨e', v', he, hen, hvn, hv0, hv1⟩ := Formalism.HermitianLatticeCounting.P.majorant_parameter_choice_holds _ _ (isTheta _ hH hHH) r
    (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a hpos.ne'
  have hgg : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (g⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hgg' : ∀ x : Fin (2 * r + k + 1) → ℂ, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hform : ∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) =
      majorantHermitianForm (Matrix.toEuclideanLin (Formalism.QuantumDeterminants.Hpk k r))
        (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b)) v' := fun b => by
    rw [form_eq _ hH, ← herm_mulVec hg (WithLp.ofLp _) v'.ofLp, WithLp.ofLp_toLp, hgg]
  have hE : g *ᵥ e'.ofLp - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
      Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) := by
    have h1 := Submodule.mem_map_of_mem
      (f := (Matrix.mulVecLin g).comp (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap) he
    rw [Submodule.map_span, Set.image_image] at h1
    simpa [mulVec_sub, hgg, -mulVec_mulVec] using h1
  have hV0 : ∀ b, b ≤ a.castSucc →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) (g *ᵥ v'.ofLp) = 0 := fun b hb => by
    rw [hform]; exact hv0 b hb
  have hV1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) (g *ᵥ v'.ofLp) =
      -Complex.I * (lenA k r z g a.succ : ℂ) := by
    rw [hform]; exact hv1
  obtain ⟨h3, -, hN⟩ := Formalism.HermitianLatticeCounting.P.nilpotent_model_computation_holds k r z hz a _ _ hE hV0
  have hpsi := Formalism.HermitianLatticeCounting.P.derivative_of_psi_holds k r z hz a _ _ 1 _ hE hV0 hV1
  have hAd := Formalism.HermitianLatticeCounting.P.matrix_adjoint_action_holds _ _ hHu g hg (g *ᵥ e'.ofLp) (g *ᵥ v'.ofLp)
  rw [hgg', hgg'] at hAd
  refine ⟨rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e'.ofLp v'.ofLp, ymat_skew _ hH _ _, ?_, fun t => ⟨_, (hN t).1, ?_, ?_⟩⟩
  · have h := ymat_hs _ hH hHH e' v'
    rw [hvn, hen, one_pow, mul_one] at h
    exact h
  · rw [← hAd, ← Matrix.smul_mul, ← Matrix.mul_smul,
      Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), exp_of_cube_eq_zero _ h3,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  · simpa using hpsi t

end GlobalTheory.UnipotentElement
