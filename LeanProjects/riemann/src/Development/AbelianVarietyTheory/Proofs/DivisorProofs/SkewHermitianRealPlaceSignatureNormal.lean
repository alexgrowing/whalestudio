import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CartanFrame

theorem exists_unitary_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * A * U = diagonal (fun i => (l i : ℂ)) := by
  have h : A.IsHermitian := hA
  refine ⟨(h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), h.eigenvalues, ?_, ?_, ?_⟩
  · exact h.eigenvectorUnitary.2.1
  · exact h.eigenvectorUnitary.2.2
  · have := h.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

theorem exists_whiten {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    ∃ S R : Matrix (Fin n) (Fin n) ℂ, R * S = 1 ∧ S * R = 1 ∧ Sᴴ * A * S = 1 := by
  obtain ⟨U, l, h1, h2, h3⟩ := exists_unitary_diag A hA
  have hl : ∀ i, 0 < l i := by
    intro i
    have hx : (fun j => U j i) ≠ 0 := by
      intro h0
      have := congrFun (congrFun h1 i) i
      have hz : ∀ j, U j i = 0 := fun j => congrFun h0 j
      simp [Matrix.mul_apply, hz] at this
    have hp := hpos _ hx
    have he : star (fun j => U j i) ⬝ᵥ A *ᵥ (fun j => U j i) = (Uᴴ * A * U) i i := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
    rw [he, h3] at hp
    simpa using hp
  have hs : ∀ i, ((Real.sqrt (l i) : ℝ) : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (Real.sqrt_pos.mpr (hl i)).ne'
  have hss : ∀ i, ((Real.sqrt (l i) : ℝ) : ℂ) * ((Real.sqrt (l i) : ℝ) : ℂ) = (l i : ℂ) := fun i => by
    exact_mod_cast Real.mul_self_sqrt (hl i).le
  have hRS : (diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)) * Uᴴ) *
      (U * diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, h1, Matrix.one_mul, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hs i)
  refine ⟨U * diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹),
    diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)) * Uᴴ, hRS, mul_eq_one_comm.mp hRS, ?_⟩
  have : (U * diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹))ᴴ * A *
      (U * diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹)) =
      (diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹))ᴴ * (Uᴴ * A * U) *
        diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)⁻¹) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [this, h3, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← hss i]
  have := hs i
  simp only [Pi.star_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  field_simp

theorem exists_frame_of_pos {n : ℕ} (N θ : Matrix (Fin n) (Fin n) ℂ) (hN : Nᴴ = N) (hθ : θ * θ = 1)
    (hiso : θᴴ * N * θ = N) (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (N * θ) *ᵥ x).re) :
    ∃ (κ : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ), IsUnit Q ∧ Qᴴ * N * Q = Formalism.REAL.Jm κ ∧
      θ * Q = Q * Formalism.REAL.Jm κ := by
  have hA : (N * θ)ᴴ = N * θ := by
    rw [conjTranspose_mul, hN]
    calc θᴴ * N = θᴴ * N * (θ * θ) := by rw [hθ, Matrix.mul_one]
      _ = N * θ := by rw [← Matrix.mul_assoc, hiso]
  obtain ⟨S, R, hRS, hSR, hS⟩ := exists_whiten (N * θ) hA hpos
  have h1 : S * Sᴴ * (N * θ) = 1 := by
    calc S * Sᴴ * (N * θ) = S * (Sᴴ * (N * θ) * S) * R := by
          simp only [Matrix.mul_assoc]; rw [hSR, Matrix.mul_one]
      _ = 1 := by rw [hS, Matrix.mul_one, hSR]
  have h2 : S * Sᴴ * N = θ := by
    calc S * Sᴴ * N = S * Sᴴ * (N * θ) * θ := by
          simp only [Matrix.mul_assoc]; rw [hθ, Matrix.mul_one]
      _ = θ := by rw [h1, Matrix.one_mul]
  have hT : (Sᴴ * N * S)ᴴ = Sᴴ * N * S := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hN, Matrix.mul_assoc]
  have hTT : (Sᴴ * N * S) * (Sᴴ * N * S) = 1 := by
    calc (Sᴴ * N * S) * (Sᴴ * N * S) = Sᴴ * (N * (S * Sᴴ * N)) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, hS]
  obtain ⟨V, μ, v1, v2, v3⟩ := exists_unitary_diag _ hT
  have hμ : ∀ i, μ i * μ i = 1 := by
    intro i
    have : diagonal (fun i => (μ i : ℂ)) * diagonal (fun i => (μ i : ℂ)) = 1 := by
      rw [← v3]
      calc Vᴴ * (Sᴴ * N * S) * V * (Vᴴ * (Sᴴ * N * S) * V)
          = Vᴴ * ((Sᴴ * N * S) * (V * Vᴴ) * (Sᴴ * N * S)) * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [v2, Matrix.mul_one, hTT, Matrix.mul_one, v1]
    rw [diagonal_mul_diagonal] at this
    have := congrFun (congrFun this i) i
    simp only [diagonal_apply_eq, one_apply_eq] at this
    exact_mod_cast this
  have hJ : Formalism.REAL.Jm (fun i => decide (0 < μ i)) = diagonal (fun i => (μ i : ℂ)) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext i
    rcases mul_self_eq_one_iff.mp (hμ i) with h | h <;> simp [h]
  refine ⟨fun i => decide (0 < μ i), S * V, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (Vᴴ * R) ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, v2, Matrix.one_mul, hSR]
  · rw [hJ, ← v3, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  · rw [hJ, ← v3, ← h2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᴴ, v2, Matrix.one_mul]

theorem exists_frame_of_isCartan {n : ℕ} (H θ : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hc : IsCartan H θ)
    (a : ℝ) (ha : a ≠ 0) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * ((a : ℂ) • Hᵀ) * P = Formalism.REAL.Jm ε ∧
      (P⁻¹ * θ * P = Formalism.REAL.Jm ε ∨ P⁻¹ * θ * P = -Formalism.REAL.Jm ε) := by
  obtain ⟨h1, h2, h3⟩ := hc
  have hT : (Hᵀ)ᴴ = Hᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa using this
  have hN : ((a : ℂ) • Hᵀ)ᴴ = (a : ℂ) • Hᵀ := by
    rw [conjTranspose_smul, hT]; simp
  have hiso : θᴴ * Hᵀ * θ = Hᵀ := by
    have := congrArg Matrix.transpose h2
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  have hq : ∀ x : Fin n → ℂ, star x ⬝ᵥ (Hᵀ * θ) *ᵥ x = θ *ᵥ x ⬝ᵥ H *ᵥ star x := by
    intro x
    rw [← mulVec_mulVec, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  have key : ∀ s : ℝ, s * s = 1 → 0 < a * s → ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧
      Pᴴ * ((a : ℂ) • Hᵀ) * P = Formalism.REAL.Jm ε ∧ (s : ℂ) • (P⁻¹ * θ * P) = Formalism.REAL.Jm ε := by
    intro s hs has
    have hs' : (s : ℂ) * (s : ℂ) = 1 := by exact_mod_cast hs
    obtain ⟨κ, Q, hQ, q1, q2⟩ := exists_frame_of_pos ((a : ℂ) • Hᵀ) ((s : ℂ) • θ) hN
      (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs', h1, one_smul])
      (by
        rw [conjTranspose_smul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hiso, Complex.star_def, Complex.conj_ofReal]
        congr 1
        linear_combination (a : ℂ) * hs')
      (by
        intro x hx
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec, dotProduct_smul, hq, ← Complex.ofReal_mul,
          smul_eq_mul, Complex.re_ofReal_mul]
        exact mul_pos has (h3 x hx))
    refine ⟨κ, Q, hQ, q1, ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul, q2, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det Q).mp hQ), Matrix.one_mul]
  rcases lt_or_gt_of_ne ha with h | h
  · obtain ⟨ε, P, p1, p2, p3⟩ := key (-1) (by norm_num) (by linarith)
    refine ⟨ε, P, p1, p2, Or.inr ?_⟩
    rw [← p3]; simp
  · obtain ⟨ε, P, p1, p2, p3⟩ := key 1 (by norm_num) (by linarith)
    refine ⟨ε, P, p1, p2, Or.inl ?_⟩
    rw [← p3]; simp

theorem exists_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ c : E, c ≠ 0 → σ c = -c → ∀ w : InfinitePlace F, ∃ (ε : Fin d → Bool) (P : Matrix (Fin d) (Fin d) ℂ), IsUnit P ∧ Pᴴ * (c • W.J.map σ).map (B.emb w).1 * P = Formalism.REAL.Jm ε ∧ (P⁻¹ * W.θ w * P = Formalism.REAL.Jm ε ∨ P⁻¹ * W.θ w * P = -Formalism.REAL.Jm ε) := by
  intro F E _ _ _ _ _ σ B d r s W hG hW c hc0 hc w
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ = (B.emb w).1 := ⟨_, rfl⟩
  have hcart := hW.cartan w
  rw [← hτ] at hcart ⊢
  have hcm : ∀ x, τ (σ x) = star (τ x) := hG.cm.2.2.2 τ
  have hsk : ∀ i j, star (τ (W.J j i)) = -τ (W.J i j) := fun i j => by
    rw [← hcm, hW.skew, map_neg]
  have hcc : star (τ c) = -τ c := by rw [← hcm, hc, map_neg]
  have hre : (τ c).re = 0 := by
    have := congrArg Complex.re hcc
    simp at this
    linarith
  have hτc : τ c = Complex.I * ((τ c).im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  have him : (τ c).im ≠ 0 := by
    intro h0
    apply hc0
    apply τ.injective
    rw [hτc, h0]; simp
  have hH : (Complex.I • W.J.map τ)ᴴ = Complex.I • W.J.map τ := by
    ext i j
    simp only [conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, star_mul', hsk]
    simp
  have hM : (c • W.J.map σ).map τ = ((-(τ c).im : ℝ) : ℂ) • (Complex.I • W.J.map τ)ᵀ := by
    ext i j
    simp only [transpose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, map_mul, hcm, hsk]
    rw [hτc]
    simp
    ring
  rw [hM]
  exact exists_frame_of_isCartan _ _ hH hcart _ (neg_ne_zero.mpr him)

end GlobalTheory.CartanFrame
