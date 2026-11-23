import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Meas

variable {k r : ℕ}

theorem uh_mul {a b : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem uh_cancel {a x : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hax : a * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hax' : (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) = Formalism.QuantumDeterminants.Hpk k r := hax
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * x := by rw [ha']
    _ = (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hax'

theorem uh_measurableSet :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : IsClosed {x : Formalism.QuantumDeterminants.Mt k r | (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact hc.measurableSet.compl

theorem ae_UH_of_quot {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : μG {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS0 : μS ≠ 0) (hS : μS {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) :
    ∀ᵐ x ∂νq, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  classical
  set B : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hBdef
  have hBm : MeasurableSet B := uh_measurableSet
  have key := hq (B.indicator 1) (measurable_one.indicator hBm)
  rw [lintegral_indicator_one hBm, hG] at key
  have hc : μS Bᶜ ≠ 0 := by
    intro h0
    apply hS0
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc μS Set.univ = μS (B ∪ Bᶜ) := by rw [Set.union_compl_self]
      _ ≤ μS B + μS Bᶜ := measure_union_le _ _
      _ = 0 := by rw [hS, h0, add_zero]
  have hle : ∀ x, μS Bᶜ * B.indicator 1 x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, ← lintegral_indicator_one hBm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
      · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ B := fun hmem =>
          hx (uh_cancel (x := Matrix.of x) hs hmem)
        have hsB : s ∈ Bᶜ := fun h => h hs
        rw [Set.indicator_of_mem hsB, Set.indicator_of_mem hsx]
        exact le_rfl
      · have hsB : s ∉ Bᶜ := fun h => h hs
        rw [Set.indicator_of_notMem hsB]
        exact zero_le
    · rw [Set.indicator_apply, if_neg hx, mul_zero]
      exact zero_le
  have h0 : μS Bᶜ * νq B = 0 := by
    rw [← lintegral_indicator_one hBm, ← lintegral_const_mul _ (measurable_one.indicator hBm)]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, μS Bᶜ * B.indicator 1 x ∂νq
        ≤ ∫⁻ x, ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂νq := lintegral_mono hle
      _ = 0 := key.symm
  have hνB : νq B = 0 := (mul_eq_zero.mp h0).resolve_left hc
  rw [ae_iff]
  exact hνB

theorem muSof_facts {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    muSof μW μN ≠ 0 ∧ muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  obtain ⟨hWs, hW0, hWb, -⟩ := hW
  obtain ⟨hNs, hN0, hNb, -⟩ := hN
  haveI := hWs
  haveI := hNs
  have hcont : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hmeas := hcont.measurable
  refine ⟨?_, ?_⟩
  · intro h0
    unfold muSof at h0
    rw [Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    have h1 : (μW.prod μN) Set.univ = 0 := by rw [h0, Measure.coe_zero, Pi.zero_apply]
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)
  · unfold muSof
    rw [Measure.map_apply hmeas uh_measurableSet]
    refine measure_mono_null (t := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ ∪
      Set.univ ×ˢ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_ ?_
    · rintro ⟨a, b⟩ hab
      by_contra hno
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq, not_or,
        not_not] at hno
      exact hab (uh_mul hno.1.1 hno.2.1)
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hWb, zero_mul]
      · rw [Measure.prod_prod, hNb, mul_zero]

end Meas

section Deg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fdeg_eq {σ : Mx k r → (H →L[ℂ] H)} {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} {d : ℝ} (hd : 0 < d)
    (hS : ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {u : H} (hu : u ≠ 0) : PI.BesselPeriodGGP.fdegH μG σ u = d := by
  obtain ⟨-, hI⟩ := hS u u u u
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r, ⟪u, σ (Matrix.of x) u⟫_ℂ * star ⟪u, σ (Matrix.of x) u⟫_ℂ =
      ((‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hpt] at hI
  rw [integral_complex_ofReal] at hI
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu4 : (0 : ℝ) < ‖u‖ ^ 4 := pow_pos hn 4
  have huu : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    · rw [Complex.ofReal_im]
      exact inner_self_im (𝕜 := ℂ) u
  have hreal : ∫ x, ‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 ∂μG = ‖u‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hI, huu]
    push_cast
    ring
  unfold PI.BesselPeriodGGP.fdegH
  rw [hreal]
  field_simp

end Deg

section Bessel

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem bessel_smul {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B) (κ : ℂ) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => κ • B x) := by
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, ‖κ‖ * C, Ws, hWs, fun v hv => ?_⟩
  · simp only [hadd v hv w hw, smul_add]
  · simp only [hsm c v hv]
    exact smul_comm κ c (B v)
  · simp only [heq h hh m hm v hv, map_smul]
    exact smul_comm κ (ψ m) _
  · rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg κ)

theorem bessel_zero {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun _ => (0 : Wp)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp, 0, [], by simp,
    fun _ _ => by simp⟩

theorem jsz_line (hU : PI.BesselMapUniq.BesselMapUniq) (hPsi : PsiConst)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hfun : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) :=
    funext fun g => hPsi k r z c g
  rw [hfun] at h0 h
  obtain ⟨a, b, hab, hlin⟩ := hU k r ε lam H σ z (fun _ => c) u Wp π hl hσ hz hT (fun _ => hc) hπ B0 B h0 h
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := hab.resolve_right (fun h => h rfl)
    have h2 := hlin x0 hx0
    rw [zero_smul, add_zero, smul_eq_zero] at h2
    exact h2.elim ha hne
  refine ⟨-(a / b), fun x hx => ?_⟩
  have h1 : b • B x = -(a • B0 x) := eq_neg_of_add_eq_zero_right (hlin x hx)
  calc B x = b⁻¹ • (b • B x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = -(a / b) • B0 x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Bessel

end Formalism.FourierDecayAlt.P.DDSmoothness
