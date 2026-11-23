import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayInputsOfDecAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundAndFarBoundAndDecGap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny

namespace GlobalTheory.DecTransport

open Matrix Finset Formalism.FourierDecayAlt.ThreeDimData in
open scoped InnerProductSpace in

lemma decE_le {q : ℕ} (hq : 1 ≤ q) {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d) :
    GlobalTheory.Count.decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q)) * d) := by
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hq)

  have key : d / Real.sqrt q - min (2 * d ^ 2) (d / Real.sqrt q) ≤ 1 := by
    rcases le_total (2 * d ^ 2) (d / Real.sqrt q) with hm | hm
    · rw [min_eq_left hm]
      have : d / Real.sqrt q ≤ d := div_le_self hd hs
      nlinarith [sq_nonneg (d - 1 / 4)]
    · rw [min_eq_right hm]; linarith
  have e : -(h / (8 * Real.sqrt q)) * d = -(h / 8) * (d / Real.sqrt q) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ h / 8)]

private lemma inv_mul_and_mul_inv_of_isCayleyU {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : PI.UpqRep.IsCayleyU k r ε P) :
    P⁻¹ * P = 1 ∧ P * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  exact ⟨Matrix.nonsing_inv_mul P hd, Matrix.mul_nonsing_inv P hd⟩

private lemma conjTranspose_mem_Kset' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : PI.UpqRep.IsCayleyU k r ε P) (hQ : PI.UpqRep.IsCayleyU k r ε Q) :
    P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  obtain ⟨⟨-, hPJ⟩, -⟩ := hP
  obtain ⟨⟨-, hQJ⟩, hQu⟩ := hQ
  have hQi : Q⁻¹ = Q.conjTranspose := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hQu)
  have hQQ : Q * Q.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hQu
  show (P * Q⁻¹).conjTranspose * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  rw [hQi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Q * P.conjTranspose * PI.UpqRep.Jm ε * (P * Q.conjTranspose)
        = Q * (P.conjTranspose * PI.UpqRep.Jm ε * P) * Q.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Q.conjTranspose * PI.UpqRep.Jm ε * Q) * Q.conjTranspose := by rw [hPJ, hQJ]
    _ = (Q * Q.conjTranspose) * PI.UpqRep.Jm ε * (Q * Q.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hQQ, Matrix.one_mul, Matrix.mul_one]

private lemma rpow_three_div_two_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_one_add' hx (by norm_num), Real.sqrt_eq_rpow]

open Matrix Finset GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap Formalism.FourierDecayAlt.B in
open scoped InnerProductSpace in

theorem decLow_of_decGap (hA : GlobalTheory.DSId.DecGap) : Formalism.FourierDecayAlt.ThreeDimData.DecLow := by
  intro k r hk ε lam h H _ _ _ σ hl hσ hg h120 P hP w₁ w₂ h₁ h₂
  have hh : 0 ≤ h := by
    have : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    linarith
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hPu)
  have hPP := inv_mul_and_mul_inv_of_isCayleyU hP

  obtain ⟨P0, hP0, hDS0⟩ := hσ
  have hP0P := inv_mul_and_mul_inv_of_isCayleyU hP0
  have hDS : PI.UpqRep.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) := by
    have h0 := GlobalTheory.CayleyChoice.isDS_conj hDS0 (conjTranspose_mem_Kset' hP hP0) (conjTranspose_mem_Kset' hP0 hP)
      (by
        calc P * P0⁻¹ * (P0 * P⁻¹) = P * (P0⁻¹ * P0) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hP0P.1, Matrix.mul_one, hPP.2])
    have hfun : (fun g => σ (P⁻¹ * g * P)) =
        (fun g => σ (P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0)) := by
      funext g
      congr 1
      calc P⁻¹ * g * P = (P0⁻¹ * P0) * (P⁻¹ * g * P) * (P0⁻¹ * P0) := by
            rw [hP0P.1, Matrix.one_mul, Matrix.mul_one]
        _ = P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0 := by simp only [Matrix.mul_assoc]
    rw [hfun]
    exact h0

  have hq : rkR ε = r + 1 := rkR_eq hk hP
  have hgap : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hq]
    have h1 := GlobalTheory.GapSizeCheck.decay_range k r h h120
    have e : (((r + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) = ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) := by
      push_cast
      exact rpow_three_div_two_eq_mul_sqrt (by positivity)
    rw [e]
    exact h1

  have ha : 0 ≤ h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by positivity
  have hab : h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ h / (8 * Real.sqrt ((r : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left hh (by positivity)
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    gcongr
    linarith
  refine ⟨Real.exp (h / 8) * Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
    ‖w₁‖ * ‖w₂‖, fun x hx => ?_⟩

  have ex : P⁻¹ * (P * x * P⁻¹) * P = x := by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPP.1, Matrix.one_mul, Matrix.mul_one]
  have hgU : P * x * P⁻¹ ∈ PI.UpqRep.UJset ε :=
    (GlobalTheory.UnitaryCayley.transport hP (P * x * P⁻¹)).1.mp (by rw [ex]; exact hx)
  have hb : ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := by
    have h0 := (hA _ ε lam H (fun g => σ (P⁻¹ * g * P)) hl hDS h hg hgap (P * x * P⁻¹) hgU w₁ h₁ w₂ h₂).2
    rw [hq] at h0
    simpa only [ex] using h0
  have hd : 0 ≤ dOp (P * x * P⁻¹) := ((GlobalTheory.Dec.dFacts_holds _ ε).1 _ hgU).1
  have hdecE : decE (r + 1) h (dOp (P * x * P⁻¹)) ≤
      Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) := by
    have h0 := decE_le (q := r + 1) (by omega) hh hd
    push_cast at h0
    exact h0

  have hcl : Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) (P * x * P⁻¹) =
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹)) := by
    first
      | rfl
      | (apply ContinuousLinearMap.coe_injective; simp [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin])
  have hGN : gN x ≤ Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) *
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
    have h1 := hs_le_op x
    have h2 : ‖Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) x‖ =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
      rw [← hcl, ← op_conj hPu x, hPi]
    rw [h2] at h1
    show Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j)) ≤ _
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))
        ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hE : Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) ≤
      Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
        gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
    exp_le_rpow ha hab (by positivity) hd (gN_pos hx) hGN
  calc ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := hb
    _ ≤ (Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹))) *
          ‖w₁‖ * ‖w₂‖ := by gcongr
    _ ≤ (Real.exp (h / 8) * (Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
          gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))))) * ‖w₁‖ * ‖w₂‖ := by gcongr
    _ = _ := by ring

theorem decLow_holds : Formalism.FourierDecayAlt.ThreeDimData.DecLow :=
  decLow_of_decGap GlobalTheory.Deep.ptBound_and_farBound_and_decGap.2.2

end GlobalTheory.DecTransport
