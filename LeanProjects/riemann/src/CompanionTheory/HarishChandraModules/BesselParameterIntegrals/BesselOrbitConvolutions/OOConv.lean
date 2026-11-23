import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OoConvOf
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.PhiReg

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

namespace G

set_option maxHeartbeats 1000000 in
theorem ooConv_of (hSch : SchurH) (hNIs : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hNI : NormInv) (hGG : GrowthG) (hDD : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD)
    (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) : CompanionTheory.D.Upq.BesselFunctionalConstruction.OOConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe' γ hγ
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, -, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1
  obtain ⟨hγi, hγγ, hγγ'⟩ := MatrixMultiplicationContinuity.uh_inv hγU
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hP1 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN
    D.μG νq hS1 l hbe w0 hw0DD
  have hP2 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN
    D.μG νq' hS2 l' hbe' w0 hw0DD
  have cont2' : ContinuousOn (fun g : Mx k r => l' (σ (γ⁻¹ * g) w0)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    hP2.1.comp (continuous_const.matrix_mul continuous_id).continuousOn (fun g hg => DDSmoothness.uh_mul hγi hg)
  have hop : ContinuousOn (fun g : Mx k r => (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))).smulRight (l (σ g w0)))
      (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have ha : ContinuousOn (fun g : Mx k r =>
        ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))))
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
      (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous.comp_continuousOn
        ((innerSL ℂ).continuous.comp_continuousOn cont2')
    exact (ha.clm_apply hP1.1).congr fun g _ => rfl
  have hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG := by
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r =>
        (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0)))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
      hop.comp mt_cont.continuousOn (fun x hx => hx)
    have := hc.aestronglyMeasurable (μ := D.μG) uh_mem_measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) hGc] at this
  refine ⟨hmeas, ?_⟩
  show ∫⁻ x, ‖(innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))‖ₑ ∂D.μG < ⊤
  simp only [enorm_smulRight]
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA _ (dd_stable hds hx w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA' _ (dd_stable hds (DDSmoothness.uh_mul hγi hx) w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa := la_fin hNI D hThrb hb0.ne' hγ
  have hpt : ∀ᵐ x ∂D.μG, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤
      ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
        ((∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)) *
          (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN))) := by
    filter_upwards [hGc] with x hx
    have hgx : γ⁻¹ * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hγi hx
    have b1 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hx
    have b2 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hgx
    have i1 : ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) w0⟫_ℂ‖ₑ ∂(D.μW.prod D.μN) =
        ∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW hN] with p hp
      rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hx)]
    have i2 : ∫⁻ q, ‖⟪v', σ (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x)) w0⟫_ℂ‖ₑ
        ∂(D.μW'.prod D.μN) =
        ∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW' hN] with q hq
      rw [hee2 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hq.1.1 hq.2.1) hgx)]
    rw [i1] at b1; rw [i2] at b2
    calc ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤ _ * _ := mul_le_mul' b2 b1
      _ = _ := by ring
  have hinner : ∀ᵐ p ∂(D.μW.prod D.μN), ∀ᵐ q ∂(D.μW'.prod D.μN),
      ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ≤
        (ENNReal.ofReal (|C1| * |C2|) *
          ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
        ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
          (-(aOf r h - AG k r - 1))‖ₑ := by
    filter_upwards [prod_ae hW hN] with p hp
    filter_upwards [prod_ae hW' hN] with q hq
    have hPU : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hQU : Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hq.1.1 hq.2.1
    have hIB := inner_bound hNI D.haarG hGc he1 he2 hb1 hb2 hb0.le hba hPU hQU hγi
    have hY := gN_Y_eq hNI hPU hQU hγU
    have e : Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ =
        Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹ := by
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    unfold Phi3
    rw [hY, e] at hIB
    calc _ ≤ _ := hIB
      _ = _ := by ring
  have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
  calc ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG
      ≤ ∫⁻ x, ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γ⁻¹ x p q ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) ∂D.μG := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        rw [← triple_lintegral_product he1 he2 γ⁻¹]; exact hx
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), triple_lintegral_swap he1 he2 γ⁻¹]
    _ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, (ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
            ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        gcongr 1
        exact lintegral_mono_ae (hinner.mono fun p hp => lintegral_mono_ae hp)
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ((ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
          ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS) := by
        congr 1
        have hc0 : ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKg.ne
        simp_rw [lintegral_const_mul' _ _ hc0]
        rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) (ENNReal.mul_lt_top ?_ hLa)
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKg

end G

end Formalism.FourierDecayAlt.P.S3dx4

end
