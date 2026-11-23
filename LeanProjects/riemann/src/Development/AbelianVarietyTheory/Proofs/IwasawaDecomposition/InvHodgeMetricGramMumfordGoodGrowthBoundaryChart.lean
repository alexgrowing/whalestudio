import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGramStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricGStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwoStatement

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem conn_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E) (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ : E) : conn (fun x => (H x)⁻¹) z ξ = -(conn H z ξ)ᵀ := by
  rw [conn_congr (H' := fun x => dualGram (H x))
    (hs.mono fun x hx => by simp only [dualGram, transpose_nonsing_inv, hx.eq]) ξ, conn_dual h hu]

theorem norm_mul_apply_le {g : ℕ} (P Q : Matrix (Fin g) (Fin g) ℂ) (p q : ℝ) (hP : ∀ i j, ‖P i j‖ ≤ p)
    (hQ : ∀ i j, ‖Q i j‖ ≤ q) (i j : Fin g) : ‖(P * Q) i j‖ ≤ g * (p * q) := by
  rw [mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin g)), ‖P i k * Q k j‖ ≤ p * q := fun k _ => by
    rw [norm_mul]
    exact mul_le_mul (hP i k) (hQ k j) (norm_nonneg _) ((norm_nonneg _).trans (hP i k))
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  simp

theorem ofLp_coordVec {n : ℕ} (k : Fin n) : (coordVec k).ofLp = Pi.single k (1 : ℂ) := by simp

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.HermFrame

theorem norm_apply_le_opNorm {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    ‖A i j‖ ≤ opNorm 1 1 A := by
  have h := gnorm_mulVec_le (PosDef.one (n := Fin g) (R := ℂ)) PosSemidef.one A (Pi.single j 1)
  have h1 : gnorm (1 : Matrix (Fin g) (Fin g) ℂ) (Pi.single j 1) = 1 := by
    rw [gnorm, form_single]; simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  set w := A *ᵥ Pi.single j 1 with hw
  have hwi : w i = A i j := by simp [hw, mulVec_single_one]
  rw [gnorm, form, one_mulVec, ← hwi]
  apply Real.le_sqrt_of_sq_le
  have e : w ⬝ᵥ star w = ∑ k, ((‖w k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem inv_hodgeGram_goodBound : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  intro n a ha g rk τ₀ B hP
  obtain ⟨ρ, c₀, C, hρ0, hρ2, hc₀, h1, h2, h3, h4⟩ :=
    GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW GlobalTheory.T.schur_complement_block_quadratic_lower_bound GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec n a g rk ha τ₀ B hP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set D : ℝ := C' * (1 + 1 / Real.log 2 + 1 / (2 * Real.pi)) with hD
  have hD0 : 0 ≤ D := mul_nonneg hC'0 (by positivity)
  set c : ℝ := max (max ((1 / c₀) * (1 / Real.log 2) ^ g) ((g.factorial : ℝ) * D ^ g))
    (max (5 * C') (50 * g * C' ^ 2)) with hc
  refine ⟨ρ, hρ0, hρ2, c, if a = 0 then 0 else g, fun v hv => ?_⟩
  set z : Fin n → ℂ := v.ofLp with hzdef
  set S : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb ha) with hS
  set Y := hodgeGram ha τ₀ B with hY
  set Yv : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ := fun u => Y u.ofLp with hYv
  set s : ℝ := ∑ k ∈ S, |Real.log ‖v k‖| with hs
  have hz1 : z ∈ punctured ha 1 := ⟨fun k => (hv.1 k).trans_le (hρ2.trans (by norm_num)), hv.2⟩
  have hpd : (Y z).PosDef := (h4 z hv).1
  have hu : IsUnit (Y z).det := (isUnit_iff_isUnit_det _).1 hpd.isUnit
  obtain ⟨hYinf, -, hdd⟩ := GlobalTheory.HodgeGramLocal.hodgeGram_local n a g rk ha τ₀ B hP z hz1

  let φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hφ : ∀ u, φ u = u.ofLp := fun u => rfl
  have hφd : ∀ ξ, fderiv ℂ φ v ξ = ξ.ofLp := fun ξ => by rw [φ.fderiv]; rfl
  have hY2 : MContDiffAt 2 Y z := hYinf.of_le (by norm_cast)
  have hYv2 : MContDiffAt 2 Yv v := fun i j =>
    (hY2 i j).comp v ((φ.restrictScalars ℝ).contDiff.contDiffAt)

  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  have hsymR : ∀ x ∈ polydisc n 1, (imPeriod ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm x hx).apply]
  have hnb : ∀ᶠ u in 𝓝 v, u.ofLp ∈ polydisc n 1 :=
    φ.continuous.continuousAt.eventually_mem ((GlobalTheory.HodgeChartRow.isOpen_polydisc n 1).mem_nhds hz1.1)
  have hevS : ∀ᶠ u in 𝓝 v, (Yv u).IsSymm := hnb.mono fun u hu' =>
    IsSymm.ext fun j k => by simp [Yv, Y, hodgeGram, (hsymR _ hu').apply j k]
  have hevH : ∀ᶠ u in 𝓝 v, (Yv u).IsHermitian := hnb.mono fun u hu' => by
    ext j k; simp [Yv, Y, hodgeGram, conjTranspose_apply, (hsymR _ hu').apply j k]
  have hddv : ∀ ξ η, mddbar Yv v ξ η = 0 := fun ξ η => by
    ext i j
    have := GlobalTheory.ddbar_comp_holo (u := fun x => Y x i j) (φ := φ) (z := v) (hY2 i j) φ.contDiff.contDiffAt ξ η
    simp only [mddbar_apply]
    rw [show (fun x => Yv x i j) = fun x => Y (φ x) i j from rfl, this, hφd, hφd]
    have h0 := congrFun (congrFun (hdd ξ.ofLp η.ofLp) i) j
    simp only [mddbar_apply] at h0
    exact h0
  have hconn : ∀ ξ, conn Yv v ξ = conn Y z ξ.ofLp := fun ξ => by
    rw [show Yv = fun x => Y (φ x) from rfl, conn_comp_holo (hY2.of_le (by norm_num)) φ.differentiableAt ξ, hφd]
    rfl

  set Kf : Fin n → ℝ := fun k => C' * gnorm (poincareGram a z) (Pi.single k 1) with hKf
  have hKf0 : ∀ k, 0 ≤ Kf k := fun k => mul_nonneg hC'0 (gnorm_nonneg _ _)
  have hKe : ∀ k i j, ‖conn Y z (Pi.single k 1) i j‖ ≤ Kf k := fun k i j =>
    (norm_apply_le_opNorm _ i j).trans (((h3 z hv).2.2 _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _)))
  have hw0 : ∀ k, 0 ≤ poinWt S v k := fun k => by
    unfold poinWt; split_ifs <;> positivity
  have hKw : ∀ k, Kf k * poinWt S v k ≤ 5 * C' := fun k => by
    have h5 := GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five n a ha ρ hρ2 v hv k
    calc Kf k * poinWt S v k = C' * (gnorm (poincareGram a z) (Pi.single k 1) * poinWt S v k) := by
          simp only [hKf]; ring
      _ ≤ C' * 5 := mul_le_mul_of_nonneg_left h5 hC'0
      _ = 5 * C' := by ring
  have hCe : ∀ k i j, ‖conn Yv v (coordVec k) i j‖ ≤ Kf k := fun k i j => by
    rw [hconn, ofLp_coordVec]; exact hKe k i j
  have hcG : ∀ ξ, conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ = -(conn Yv v ξ)ᵀ :=
    conn_inv Yv v (hYv2.of_le one_le_two) hu hevS
  have hcurvG : ∀ ξ η, curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ η =
      -((conn Yv v η)ᵀᴴ * conn Yv v ξ)ᵀ := GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram Yv v hYv2 hu hevS hevH hddv
  have hdelG : ∀ ξ η, mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x η) v ξ -
      mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x ξ) v η =
      -(conn Yv v η * conn Yv v ξ - conn Yv v ξ * conn Yv v η)ᵀ := GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram Yv v hYv2 hu hevS

  obtain ⟨hts, hlog⟩ := GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo n a ha ρ hρ2 v hv
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc0 : 0 ≤ c := (by positivity : (0:ℝ) ≤ 5 * C').trans ((le_max_left _ _).trans (le_max_right _ _))
  have hcA : (1 / c₀) * (1 / Real.log 2) ^ g ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hcB : (g.factorial : ℝ) * D ^ g ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hc5 : 5 * C' ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hc50 : 50 * g * C' ^ 2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hE : 1 / c₀ ≤ c * s ^ (if a = 0 then 0 else g) ∧
      (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ c * s ^ (if a = 0 then 0 else g) := by
    by_cases ha0 : a = 0
    · rw [if_pos ha0, pow_zero, mul_one]
      have hs' : s / (2 * Real.pi) = 0 := by rw [← hts]; subst ha0; simp
      refine ⟨?_, ?_⟩
      · refine le_trans ?_ hcA
        have : (1 : ℝ) ≤ (1 / Real.log 2) ^ g := one_le_pow₀ (by rw [le_div_iff₀ hl2]; linarith)
        have hc1 : 0 ≤ 1 / c₀ := by positivity
        nlinarith
      · rw [hs', add_zero, mul_one]
        refine le_trans ?_ hcB
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC'0 ?_ g) (Nat.cast_nonneg _)
        rw [hD]
        have : (1 : ℝ) ≤ 1 + 1 / Real.log 2 + 1 / (2 * Real.pi) := by
          have : 0 ≤ 1 / Real.log 2 := by positivity
          have : 0 ≤ 1 / (2 * Real.pi) := by positivity
          linarith
        nlinarith
    · rw [if_neg ha0]
      have hs2 : Real.log 2 ≤ s := hlog (Nat.pos_of_ne_zero ha0)
      refine ⟨?_, ?_⟩
      · calc 1 / c₀ = ((1 / c₀) * (1 / Real.log 2) ^ g) * Real.log 2 ^ g := by
              rw [mul_assoc, ← mul_pow, one_div_mul_cancel hl2.ne', one_pow, mul_one]
          _ ≤ c * s ^ g := mul_le_mul hcA (pow_le_pow_left₀ hl2.le hs2 g) (by positivity) hc0
      · have h1s : 1 ≤ s / Real.log 2 := (one_le_div hl2).2 hs2
        have hM : C' * (1 + s / (2 * Real.pi)) ≤ D * s := by
          have e : D * s = C' * s + C' * (s / Real.log 2) + C' * (s / (2 * Real.pi)) := by
            rw [hD]; ring
          have : C' ≤ C' * (s / Real.log 2) := le_mul_of_one_le_right hC'0 h1s
          have : 0 ≤ C' * s := mul_nonneg hC'0 hs0
          rw [e]; nlinarith
        have hM0 : 0 ≤ C' * (1 + s / (2 * Real.pi)) := by positivity
        calc (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ (g.factorial : ℝ) * (D * s) ^ g :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM g) (Nat.cast_nonneg _)
          _ = ((g.factorial : ℝ) * D ^ g) * s ^ g := by rw [mul_pow]; ring
          _ ≤ c * s ^ g := mul_le_mul_of_nonneg_right hcB (by positivity)
  refine ⟨hpd, fun i k => (hYv2.inv hu) i k, ?_⟩
  refine ⟨fun i j => ?_, ?_, fun k i j => ?_, fun k l i j => ?_, fun k l i j => ?_⟩
  · show ‖((imPeriod ha τ₀ B z).map Complex.ofReal)⁻¹ i j‖ ≤ _
    exact (GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef g (imPeriod ha τ₀ B z) c₀ hc₀ (h1 z hv) i j).trans hE.1
  · show ‖((Y z)⁻¹).det‖⁻¹ ≤ _
    rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_inv]
    have hT0 : 0 ≤ 1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)) := by
      have : 0 ≤ ∑ i : Fin a, tlog (z (Fin.castLE ha i)) :=
        Finset.sum_nonneg fun i _ => (tlog_pos (hv.2 i) (hz1.1 _)).le
      linarith
    have hPSD : (imPeriod ha τ₀ B z).PosSemidef := by
      have := (h1 z hv).add (PosSemidef.one.smul hc₀.le)
      simpa using this
    have hMPSD : ((C' * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ) -
        imPeriod ha τ₀ B z).PosSemidef := by
      have := (h2 z hv).add ((PosSemidef.one (n := Fin g) (R := ℝ)).smul
        (mul_nonneg (sub_nonneg.2 (le_max_left C 0)) hT0))
      convert this using 1
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hdet := GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow g (imPeriod ha τ₀ B z) _ (mul_nonneg hC'0 hT0) hPSD hMPSD
    refine hdet.trans ?_
    rw [hts]; exact hE.2
  · rw [hcG, Matrix.neg_apply, transpose_apply, norm_neg]
    exact (mul_le_mul_of_nonneg_right (hCe k j i) (hw0 k)).trans ((hKw k).trans hc5)
  · rw [hcurvG, Matrix.neg_apply, transpose_apply, norm_neg]
    have hP : ∀ p q, ‖(conn Yv v (coordVec l))ᵀᴴ p q‖ ≤ Kf l := fun p q => by
      rw [conjTranspose_apply, transpose_apply, norm_star]; exact hCe l p q
    have hprod := norm_mul_apply_le _ _ (Kf l) (Kf k) hP (hCe k) j i
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    calc ‖((conn Yv v (coordVec l))ᵀᴴ * conn Yv v (coordVec k)) j i‖ * (poinWt S v k * poinWt S v l)
        ≤ g * (Kf l * Kf k) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right hprod (mul_nonneg (hw0 k) (hw0 l))
      _ = g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) hg0
      _ ≤ 50 * g * C' ^ 2 := by nlinarith [sq_nonneg C']
      _ ≤ c := hc50
  · rw [hdelG, Matrix.neg_apply, transpose_apply, norm_neg, Matrix.sub_apply]
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    have hA := norm_mul_apply_le _ _ (Kf l) (Kf k) (hCe l) (hCe k) j i
    have hB := norm_mul_apply_le _ _ (Kf k) (Kf l) (hCe k) (hCe l) j i
    calc ‖(conn Yv v (coordVec l) * conn Yv v (coordVec k)) j i - (conn Yv v (coordVec k) * conn Yv v (coordVec l)) j i‖
          * (poinWt S v k * poinWt S v l)
        ≤ (g * (Kf l * Kf k) + g * (Kf k * Kf l)) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hA hB)) (mul_nonneg (hw0 k) (hw0 l))
      _ = 2 * g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ 2 * g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) (by positivity)
      _ = 50 * g * C' ^ 2 := by ring
      _ ≤ c := hc50

end GlobalTheory.HodgeInvGood
