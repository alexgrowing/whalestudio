import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.BesselIntg

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem norm_psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ‖psi k r z c g‖ = 1 :=
  Formalism.FourierDecayAlt.P.S3dx6.norm_psi z c g

theorem norm_Psi_le (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {p : PairSp k r} (hp : InPair L p) (x : Mt k r) :
    ‖Psi L w0 v v' ξ ξ' γ p x‖ ≤ ‖ξ‖ * ‖ξ'‖ *
      (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
        ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := by
  rw [Psi_eq, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_mul, norm_mul,
    norm_mul, norm_star, norm_star, norm_psi_one, norm_psi_one,
    Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz'.2 L.hπ' _ hp.2.2.1, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz.2 L.hπ _ hp.1]
  nlinarith [norm_nonneg ξ, norm_nonneg ξ',
    norm_nonneg ⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ,
    norm_nonneg ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ]

theorem prod_coef_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (v v' w0 : H)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {M y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) :
    ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖ ≤
      (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) := by
  have hMy : M * y ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hM hy
  have hMi : M⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hM
  have h1 := hC1 _ hMy
  have h2 := hC2 _ hy
  have hn1 : 0 ≤ Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hn2 : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hinv : Formalism.FourierDecayAlt.B.gN (M * y) = Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) := by
    rw [← Matrix.mul_inv_rev, ((hNI k r).2 _ hMy).1]
  have hconv := Formalism.FourierDecayAlt.P.S3dx6.conv_pt hNI hb hab hy hMi
  rw [((hNI k r).2 _ hM).1] at hconv
  calc ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖
      ≤ (|C1| * Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a)) * (|C2| * Formalism.FourierDecayAlt.B.gN y ^ (-a)) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn1))
          (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn2)) (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) hn1)
    _ = (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (-a) * Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) ^ (-a)) := by
        rw [hinv]; ring
    _ ≤ (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) :=
        mul_le_mul_of_nonneg_left hconv (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem meas_gN_rpow (e : ℝ) : Measurable fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ e :=
  (Formalism.FourierDecayAlt.P.S3dx6.gN_mt_cont (k := k) (r := r)).measurable.pow_const e

theorem lint_G_bound (L : LocBessel k r) {μG : Measure (Mt k r)}
    (hμG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hI : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG ≤
      ENNReal.ofReal (‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
        Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) := by
  have hp0 := hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hhU := uh_of_uw hh
  have hnU := uh_of_n hn
  have hh'U := uh_of_uw hh'
  have hn'U := uh_of_n hn'
  have hhi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hhU
  have hni := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hnU
  have hh'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh'U
  have hn'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hn'U
  set A := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ with hA
  set B := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ with hB
  set M := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 with hM
  have hAU : A ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhi hni) hγ
  have hBU : B ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hh'i hn'i
  have hMU : M ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hAU hn'U) hh'U
  have hMB : M * B = A := by
    rw [hM, hB, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.2.1) (Matrix.of p.2.1)⁻¹, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hh'U).1,
      Matrix.one_mul, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hn'U).1, Matrix.mul_one]
  have hlm : Measurable (lmulM (k := k) (r := r) B) :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (f := fun _ => ((B : Matrix _ _ ℂ) : Mt k r)) measurable_const measurable_id
  have hmp : MeasurePreserving (lmulM (k := k) (r := r) B) μG μG := ⟨hlm, hμG.2.2.2 B hBU⟩
  set K1 : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * Formalism.FourierDecayAlt.B.gN M ^ (-b) with hK1
  have hpt : ∀ᵐ x ∂μG, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ≤
      ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) := by
    filter_upwards [ae_mem_sk hμG] with x hx
    have hBx : B * Matrix.of x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hBU hx
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have e1 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x = M * (B * Matrix.of x) := by
      rw [← Matrix.mul_assoc, hMB]
    calc ‖Psi L w0 v v' ξ ξ' γ p x‖
        ≤ ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
          ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := norm_Psi_le L w0 v v' ξ ξ' γ hp0 x
      _ = ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ (M * (B * Matrix.of x)) w0⟫_ℂ‖ * ‖⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ‖) := by
          rw [e1]
      _ ≤ ‖ξ‖ * ‖ξ'‖ * ((|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b))) :=
          mul_le_mul_of_nonneg_left (prod_coef_le hNI hb hab v v' w0 hC1 hC2 hMU hBx)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a) := by
          rw [hK1]; show _ = _ * Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a); ring
  have hK1n : 0 ≤ K1 := by
    rw [hK1]
    have := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg M) (-b)
    positivity
  have hf : Measurable fun y : Mt k r => ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) :=
    ENNReal.measurable_ofReal.comp ((meas_gN_rpow (b - a)).const_mul K1)
  calc ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG
      ≤ ∫⁻ x, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) ∂μG := lintegral_mono_ae hpt
    _ = ∫⁻ y, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) ∂μG := by
        rw [← lintegral_map hf hlm, hmp.map_eq]
    _ = ENNReal.ofReal (∫ y, K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a) ∂μG) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hI.const_mul K1)]
        exact Filter.Eventually.of_forall fun y =>
          mul_nonneg hK1n (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _)
    _ = _ := by
        rw [integral_const_mul, hK1]
        unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
        rw [← hM]
        ring_nf

end Formalism.MainNotions.S.Pv.AmpDDPf
