import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBoxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpBall

theorem isIdent_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (h : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ G.det ≠ 0 := by
  obtain ⟨h1, h2⟩ := h (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ))
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ))
  set N := Pᵀ * A (σ.symm τ)
  have hN : N * mat x τ = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hN' : mat x τ * N = 1 := mul_eq_one_comm.1 hN
  refine ⟨Matrix.det_ne_zero_of_left_inverse hN, ?_⟩
  have hA : A (σ.symm τ) = P * N := by
    calc A (σ.symm τ) = A (σ.symm τ) * (mat x τ * N) := by rw [hN', Matrix.mul_one]
      _ = P * N := by rw [← Matrix.mul_assoc, h2]
  have hJ : J * J = 1 := by
    simp [J, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [P, permM, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]
    split_ifs <;> simp
  set D := Pᵀ * J * P
  have hD : D * D = 1 := by
    calc D * D = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [D, Matrix.mul_assoc]
      _ = Pᵀ * (J * J) * P := by rw [permM_mul_transpose]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, transpose_mul_permM]
  have hDdet : D.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hD
  have hNdet : N.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hN'
  have key : -(G.map τ.1)ᵀ = Nᴴ * D * N := by
    rw [← h1, hA, Matrix.conjTranspose_mul, hPc]
    simp only [D, Matrix.mul_assoc]
  have hdet : (-(G.map τ.1)ᵀ).det ≠ 0 := by
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hNdet) hDdet) hNdet
  intro hG
  apply hdet
  rw [Matrix.det_neg, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hG, map_zero, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem riemHaar_frBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI
  have hx : ∀ τ, (mat x τ).det ≠ 0 := fun τ => (isIdent_det hI τ).1
  by_cases hd : Ψ.card * (r ^ 2 - 1) = 0
  · refine ⟨1, one_pos, fun ε _ _ => ?_⟩
    rw [hd, pow_zero, ENNReal.ofReal_one]
    exact GlobalTheory.T.riemannianHaar_le_one_of_dim_zero E r Ψ G x hr hx hd _
  have hΨ : 0 < Ψ.card := Nat.pos_of_ne_zero fun h => hd (by rw [h, zero_mul])
  obtain ⟨τ₀, hτ₀⟩ := Finset.card_pos.1 hΨ
  have hG : G.det ≠ 0 := (isIdent_det hI ⟨τ₀, hτ₀⟩).2
  have hr2 : 3 ≤ r ^ 2 - 1 := by
    have : r ≠ 1 := fun h => hd (by rw [h]; simp)
    have : 2 ≤ r := by omega
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have hd3 : 3 ≤ Ψ.card * (r ^ 2 - 1) := le_trans hr2 (Nat.le_mul_of_pos_left _ hΨ)
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hup⟩ := GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar E r Ψ G hG lam
  obtain ⟨ε₀, hε₀, hcov⟩ := GlobalTheory.T.frameBall_subset_expChart_image_frameBox E r Ψ G x hG hx δ hδ
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < 2 * ε} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b,
    ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} with hs
  have hs' : s = Metric.ball 0 δ ∩ Subtype.val ⁻¹' S := by
    ext X; simp [hs, hS, mem_ball_zero_iff]
  have hsm : MeasurableSet s := by
    rw [hs']; exact measurableSet_ball.inter (measurable_subtype_coe hSm)
  have hsb : s ⊆ Metric.ball 0 δ := by rw [hs']; exact Set.inter_subset_left
  have h1 : riemHaar Ψ G x (frBall Ψ G x ε) ≤ 2 * lam s := by
    calc riemHaar Ψ G x (frBall Ψ G x ε)
        ≤ tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
          unfold riemHaar; rw [← hmap]; exact measure_mono (hcov ε hε hεε)
      _ ≤ 2 * lam s := hup s hsm hsb
  have h2 : lam s ≤ riemLie Ψ G x S := by
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm, hs']
    exact measure_mono Set.inter_subset_right
  have h3 := GlobalTheory.T.riemannianLieMeasure_frameBox_le E r κ p q Ψ G x σ A e hr hI (2 * ε) (by positivity)
  have h4 : 2 * lam s ≤ 2 * ENNReal.ofReal ((3 * (2 * ε)) ^ (Ψ.card * (r ^ 2 - 1))) := by
    gcongr; exact h2.trans h3
  refine h1.trans (h4.trans ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  set d := Ψ.card * (r ^ 2 - 1)
  have e1 : (8 * ε) ^ d = (4 / 3 : ℝ) ^ d * (3 * (2 * ε)) ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ d := by
    calc (2 : ℝ) ≤ (4 / 3) ^ 3 := by norm_num
      _ ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd3
  rw [e1]
  exact mul_le_mul_of_nonneg_right e2 (by positivity)

end GlobalTheory.CovTop.VolUp.UpBall
