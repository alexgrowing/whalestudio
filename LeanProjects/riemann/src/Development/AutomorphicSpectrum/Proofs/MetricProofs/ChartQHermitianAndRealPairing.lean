import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLatticeStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

section Real
variable {g : ℕ}

theorem comp_det (Pr Y : Matrix (Fin g) (Fin g) ℝ) (hPP : Pr * Pr = Pr) (hPT : Prᵀ = Pr) (c : ℝ)
    (hc : 0 < c) (hlow : ∀ v : Fin g → ℝ, Pr *ᵥ v = v → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ Y *ᵥ v) :
    IsUnit (Pr * Y * Pr + (1 - Pr)).det := by
  refine Ne.isUnit fun h0 => ?_
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hx0
  set p : Fin g → ℝ := Pr *ᵥ x with hp
  set q : Fin g → ℝ := x - p with hq
  have hpp : Pr *ᵥ p = p := by rw [hp, Matrix.mulVec_mulVec, hPP]
  have hPq : Pr *ᵥ q = 0 := by rw [hq, Matrix.mulVec_sub, hpp, hp, sub_self]
  have hsymm : ∀ a b : Fin g → ℝ, a ⬝ᵥ Pr *ᵥ b = (Pr *ᵥ a) ⬝ᵥ b := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPT]
  have hexp : (Pr * Y * Pr + (1 - Pr)) *ᵥ x = Pr *ᵥ (Y *ᵥ p) + q := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  have h1 : x ⬝ᵥ (Pr *ᵥ (Y *ᵥ p) + q) = 0 := by rw [← hexp, hx, dotProduct_zero]
  have h2 : x ⬝ᵥ Pr *ᵥ (Y *ᵥ p) = p ⬝ᵥ Y *ᵥ p := by rw [hsymm]
  have h3 : x ⬝ᵥ q = q ⬝ᵥ q := by
    have : x = p + q := by rw [hq]; abel
    have h4 : p ⬝ᵥ q = 0 := by
      rw [hp, ← hsymm, hPq, dotProduct_zero]
    conv_lhs => rw [this]
    rw [add_dotProduct, h4, zero_add]
  rw [dotProduct_add, h2, h3] at h1
  have h5 := hlow p hpp
  have h6 : 0 ≤ p ⬝ᵥ p := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h7 : 0 ≤ q ⬝ᵥ q := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h8 : p ⬝ᵥ p = 0 := by
    have : c * (p ⬝ᵥ p) ≤ 0 := by linarith
    nlinarith
  have h9 : q ⬝ᵥ q = 0 := by
    have : 0 ≤ c * (p ⬝ᵥ p) := by positivity
    linarith
  have hp0 : p = 0 := dotProduct_self_eq_zero.1 h8
  have hq0 : q = 0 := dotProduct_self_eq_zero.1 h9
  have : x = p + q := by rw [hq]; abel
  rw [this, hp0, hq0, add_zero]

theorem compInv_facts (Pr Y : Matrix (Fin g) (Fin g) ℝ) (hPP : Pr * Pr = Pr) (hPT : Prᵀ = Pr)
    (hYT : Yᵀ = Y) (c : ℝ) (hc : 0 < c)
    (hlow : ∀ v : Fin g → ℝ, Pr *ᵥ v = v → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ Y *ᵥ v) :
    (compInv Pr Y)ᵀ = compInv Pr Y ∧ compInv Pr Y * Y * Pr = Pr := by
  have hdet := comp_det Pr Y hPP hPT c hc hlow
  set M : Matrix (Fin g) (Fin g) ℝ := Pr * Y * Pr + (1 - Pr) with hM
  have hMT : Mᵀ = M := by
    simp only [hM, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, hPT, hYT, Matrix.mul_assoc]
  have hMP : M * Pr = Pr * Y * Pr := by
    rw [hM, add_mul, Matrix.mul_assoc (Pr * Y), hPP, sub_mul, one_mul, hPP, sub_self, add_zero]
  have hPM : Pr * M = Pr * Y * Pr := by
    rw [hM, mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, mul_sub, mul_one, hPP, sub_self,
      add_zero]
  have hcomm : M⁻¹ * Pr = Pr * M⁻¹ := by
    have h1 : M⁻¹ * (M * Pr) * M⁻¹ = M⁻¹ * (Pr * M) * M⁻¹ := by rw [hMP, hPM]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one] at h1
    exact h1.symm
  have hG : compInv Pr Y = M⁻¹ * Pr := by
    simp only [compInv]
    rw [← hM, ← hcomm, Matrix.mul_assoc, hPP]
  constructor
  · simp only [compInv]
    rw [← hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hMT, hPT,
      Matrix.mul_assoc]
  · rw [hG, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pr, ← hMP, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, one_mul]

theorem im_form (G : Matrix (Fin g) (Fin g) ℝ) (a b a' b' : Fin g → ℝ) :
    ((fun k => (a k : ℂ) + (b k : ℂ) * Complex.I) ⬝ᵥ G.map (fun x : ℝ => (x : ℂ)) *ᵥ
      star (fun k => (a' k : ℂ) + (b' k : ℂ) * Complex.I)).im =
      b ⬝ᵥ G *ᵥ a' - a ⬝ᵥ G *ᵥ b' := by
  simp only [dotProduct, mulVec, Complex.im_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im]
  ring

end Real

section Rel
variable {g : ℕ}

theorem rel_im (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τᵀ = τ) (G Pr : Matrix (Fin g) (Fin g) ℝ)
    (hGT : Gᵀ = G) (hGY : G * τ.map Complex.im * Pr = Pr) (u u' v v' : Fin g → ℤ)
    (hv : Pr *ᵥ (fun k => (v k : ℝ)) = fun k => (v k : ℝ))
    (hv' : Pr *ᵥ (fun k => (v' k : ℝ)) = fun k => (v' k : ℝ)) :
    (((fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G.map (fun x : ℝ => (x : ℂ)) *ᵥ
      star ((fun k => (u' k : ℂ)) + τ *ᵥ (fun k => (v' k : ℂ)))).im =
      ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ) := by
  have hsplit : ∀ u v : Fin g → ℤ, (fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ)) =
      fun k => ((((fun k => (u k : ℝ)) + τ.map Complex.re *ᵥ (fun k => (v k : ℝ))) k : ℝ) : ℂ) +
        (((τ.map Complex.im *ᵥ (fun k => (v k : ℝ))) k : ℝ) : ℂ) * Complex.I := by
    intro u v
    funext k
    apply Complex.ext
    · simp [mulVec, dotProduct, Complex.re_sum]
    · simp [mulVec, dotProduct, Complex.im_sum]
  rw [hsplit u v, hsplit u' v', im_form]
  have hGb : ∀ w : Fin g → ℝ, Pr *ᵥ w = w → G *ᵥ (τ.map Complex.im *ᵥ w) = w := by
    intro w hw
    have h1 : (G * τ.map Complex.im * Pr) *ᵥ w = Pr *ᵥ w := by rw [hGY]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec] at h1
    exact h1
  have hXT : (τ.map Complex.re)ᵀ = τ.map Complex.re := by
    rw [← Matrix.transpose_map, hτ]
  have hGsym : ∀ p q : Fin g → ℝ, p ⬝ᵥ G *ᵥ q = (G *ᵥ p) ⬝ᵥ q := by
    intro p q
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hGT]
  have hXsym : ∀ p q : Fin g → ℝ, p ⬝ᵥ τ.map Complex.re *ᵥ q = (τ.map Complex.re *ᵥ p) ⬝ᵥ q := by
    intro p q
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hXT]
  rw [hGsym, hGb _ hv, hGb _ hv', dotProduct_add, add_dotProduct, hXsym]
  have h4 : ∀ p q : Fin g → ℤ, ((p ⬝ᵥ q : ℤ) : ℝ) =
      (fun k => (p k : ℝ)) ⬝ᵥ (fun k => (q k : ℝ)) := by
    intro p q
    simp [dotProduct]
  push_cast
  rw [h4, h4]
  ring

theorem pr_int (S : Matrix (Fin g) (Fin g) ℤ) (Pr : Matrix (Fin g) (Fin g) ℝ) (hP : IsKerProj S Pr)
    (hST : Sᵀ = S) (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    Pr *ᵥ (fun k => (u k : ℝ)) = 0 := by
  obtain ⟨N, w, hN, hw⟩ := GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel g S hST u hu
  obtain ⟨hPP, hPT, hker⟩ := hP
  set ur : Fin g → ℝ := fun k => (u k : ℝ) with hur
  set wr : Fin g → ℝ := fun k => (w k : ℝ) with hwr
  set p : Fin g → ℝ := Pr *ᵥ ur with hp
  have hSp : S.map (fun x : ℤ => (x : ℝ)) *ᵥ p = 0 :=
    (hker p).2 (by rw [hp, Matrix.mulVec_mulVec, hPP])
  have hSRT : (S.map (fun x : ℤ => (x : ℝ)))ᵀ = S.map (fun x : ℤ => (x : ℝ)) := by
    rw [← Matrix.transpose_map, hST]
  have h1 : (N : ℝ) • ur = S.map (fun x : ℤ => (x : ℝ)) *ᵥ wr := by
    funext k
    have := congrFun hw k
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct] at this
    simp only [hur, hwr, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.map_apply]
    exact_mod_cast this
  have h2 : p ⬝ᵥ p = p ⬝ᵥ ur := by
    have hPp : Pr *ᵥ p = p := by rw [hp, Matrix.mulVec_mulVec, hPP]
    calc p ⬝ᵥ p = p ⬝ᵥ (Pr *ᵥ ur) := rfl
      _ = (Pr *ᵥ p) ⬝ᵥ ur := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPT]
      _ = p ⬝ᵥ ur := by rw [hPp]
  have h3 : (N : ℝ) * (p ⬝ᵥ ur) = 0 := by
    rw [← smul_eq_mul, ← dotProduct_smul, h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hSRT, hSp, zero_dotProduct]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h4 : p ⬝ᵥ p = 0 := by
    rw [h2]
    exact (mul_eq_zero.1 h3).resolve_left hN'
  exact dotProduct_self_eq_zero.1 h4

end Rel

section Chart
variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem limitForm_period_symm {L : Flat.LogPeriods n a g Λ} {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ}
    {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}
    (h : IsChart L bas A T0 B c ρ) : (T0 0)ᵀ = T0 0 := by
  have hBT : ∀ j, (B j)ᵀ = B j := fun j => GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (h.B_psd j)
  let ws : ℕ → Fin n → ℂ := fun m k => if k.val < a then -((m : ℂ) + 1) else 0
  have hmem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      simp only [ws, hi, if_true]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp
      linarith
    · simp [ws, not_lt.2 hk]
  have hexp : Tendsto (fun m : ℕ => Complex.exp (-((m : ℂ) + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ m : ℕ, ‖Complex.exp (-((m : ℂ) + 1))‖ = Real.exp (-((m : ℝ) + 1)) := by
      intro m
      rw [Complex.norm_exp]
      simp
    simp only [e]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
  have hz : Tendsto (fun m => expCover a (ws m)) atTop (𝓝 (0 : Fin n → ℂ)) := by
    rw [tendsto_pi_nhds]
    intro k
    by_cases hk : k.val < a
    · simpa [expCover, ws, hk] using hexp
    · simp [expCover, ws, hk]
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hlim : Tendsto (fun m => T0 (expCover a (ws m))) atTop (𝓝 (T0 0)) :=
    ((h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz
  have each : ∀ m, (T0 (expCover a (ws m)))ᵀ = T0 (expCover a (ws m)) := by
    intro m
    have h1 := h.sym _ (hmem m)
    simp only [tauAt] at h1
    have h3 : (∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ)))ᵀ =
        ∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
          (B j).map (fun x : ℤ => (x : ℂ)) := by
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_smul, ← Matrix.transpose_map, hBT]
    rw [Matrix.transpose_add, h3] at h1
    exact add_right_cancel h1
  have hc1 : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => Nᵀ) := continuous_id.matrix_transpose
  exact tendsto_nhds_unique ((hc1.tendsto _).comp hlim) (hlim.congr fun m => (each m).symm)

theorem lower_center {L : Flat.LogPeriods n a g Λ} {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ}
    {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}
    (h : IsChart L bas A T0 B c ρ) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((T0 0).map Complex.im *ᵥ v) := by
  have hSR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hker : ∀ j, (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
    intro j
    have h0 : v ⬝ᵥ ((∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ v) = 0 := by
      rw [← hSR, hv]; simp
    rw [Matrix.sum_mulVec, dotProduct_sum] at h0
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ v) := by
      intro i _
      simpa using (h.B_psd i).dotProduct_mulVec_nonneg v
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
    exact ((h.B_psd j).dotProduct_mulVec_zero_iff v).1 (by simpa using h1)
  have := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower
    0 (Metric.mem_ball_self h.ρ_pos) 0 (fun j hj => (hj rfl).elim) (fun j _ => rfl) v
    (fun j _ => hker j)
  simpa using this

end Chart

theorem limit_form : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → (chartQ Pr A T0 0).IsHermitian ∧ (∀ x x' : chartW bas B, (chartPer bas A T0 B x ⬝ᵥ chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x')).im = L.E x x') ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x) = 0) ∧ ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re ∧ ((v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ p = chartPer bas A T0 B x}) := by
  intro n a g Λ _ L bas A T0 B c ρ Pr h hP
  classical
  have hSR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hSPSD : ((∑ j, B j).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    rw [hSR]
    exact posSemidef_sum _ fun j _ => h.B_psd j
  have hST : (∑ j, B j)ᵀ = ∑ j, B j := GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef hSPSD
  have hPkeep := hP
  obtain ⟨hPP, hPT, hker⟩ := hP
  have hτ : (T0 0)ᵀ = T0 0 := limitForm_period_symm h
  have hYT : ((T0 0).map Complex.im)ᵀ = (T0 0).map Complex.im := by
    rw [← Matrix.transpose_map, hτ]
  have hlow := lower_center h
  obtain ⟨hGT, hGY⟩ := compInv_facts Pr ((T0 0).map Complex.im) hPP hPT hYT c h.c_pos
    (fun v hv => hlow v ((hker v).2 hv))
  have hGCh : ((compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ))).IsHermitian := by
    ext i j
    have := congrFun (congrFun hGT i) j
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hdet : IsUnit (A 0).det := Ne.isUnit h.A_det
  have hdetH : IsUnit ((A 0)ᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact Ne.isUnit (star_ne_zero.2 h.A_det)
  have hdetT : IsUnit ((A 0)ᵀ).det := by
    rw [Matrix.det_transpose]; exact hdet
  have hQh : (chartQ Pr A T0 0).IsHermitian := by
    have h1 := Matrix.isHermitian_mul_mul_conjTranspose (A 0)⁻¹ hGCh
    rw [Matrix.conjTranspose_nonsing_inv] at h1
    exact h1
  have hQ2 : A 0 * chartQ Pr A T0 0 * (A 0)ᴴ =
      (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) := by
    simp only [chartQ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, mul_one]
  have hconj : ∀ y y' : Fin g → ℂ, ((A 0)ᵀ *ᵥ y) ⬝ᵥ chartQ Pr A T0 0 *ᵥ star ((A 0)ᵀ *ᵥ y') =
      y ⬝ᵥ (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) *ᵥ star y' := by
    intro y y'
    rw [← hQ2, Matrix.mulVec_transpose, Matrix.mulVec_transpose, Matrix.star_vecMul,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hform := form_coords bas L.E h.form L.alt
  have hWmem : ∀ x, x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := by
    intro x
    simp only [chartW, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply]
  have hmk : ∀ (u v : Fin g → ℤ), (∑ j, B j) *ᵥ v = 0 → mk bas u v ∈ chartW bas B := by
    intro u v hv
    rw [hWmem, vCo_mk]; exact hv
  have hper : ∀ x : chartW bas B, chartPer bas A T0 B x =
      (A 0)ᵀ *ᵥ (cst (uCo bas (x : Λ)) + T0 0 *ᵥ cst (vCo bas (x : Λ))) := fun x => rfl
  have hcast : ∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 →
      Pr *ᵥ (fun k => (v k : ℝ)) = fun k => (v k : ℝ) := by
    intro v hv
    refine (hker _).1 ?_
    funext k
    have := congrFun hv k
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at this ⊢
    exact_mod_cast this
  have hrel : ∀ u u' v v' : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → (∑ j, B j) *ᵥ v' = 0 →
      (((fun k => (u k : ℂ)) + T0 0 *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ
        (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun k => (u' k : ℂ)) + T0 0 *ᵥ (fun k => (v' k : ℂ)))).im =
        ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ) := fun u u' v v' hv hv' =>
    rel_im (T0 0) hτ _ Pr hGT hGY u u' v v' (hcast v hv) (hcast v' hv')
  have hrad : ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → u ⬝ᵥ v = 0) →
      ∀ x' : chartW bas B, L.E (mk bas u 0) x' = 0 := by
    intro u hu x'
    rw [hform, vCo_mk, uCo_mk, hu _ ((hWmem _).1 x'.2)]
    simp
  have hkerG : ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → u ⬝ᵥ v = 0) →
      (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun k => (u k : ℂ)) = 0 := by
    intro u hu
    have h1 := pr_int (∑ j, B j) Pr hPkeep hST u hu
    have h2 : compInv Pr ((T0 0).map Complex.im) *ᵥ (fun k => (u k : ℝ)) = 0 := by
      simp only [compInv]
      rw [← Matrix.mulVec_mulVec, h1, mulVec_zero]
    funext k
    have h3 := congrFun h2 k
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at h3 ⊢
    exact_mod_cast h3
  refine ⟨hQh, fun x x' => ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [hper, hper, hconj, hform]
    have h1 := hrel (uCo bas (x : Λ)) (uCo bas (x' : Λ)) (vCo bas (x : Λ)) (vCo bas (x' : Λ))
      ((hWmem _).1 x.2) ((hWmem _).1 x'.2)
    exact h1
  · have hv0 : vCo bas (x : Λ) = 0 := by
      funext i
      have h1 := hx ⟨mk bas (Pi.single i 1) 0, hmk _ _ (by simp)⟩
      rw [hform] at h1
      simpa [vCo_mk, uCo_mk] using h1
    have hu : ∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → uCo bas (x : Λ) ⬝ᵥ v = 0 := by
      intro v hv
      have h1 := hx ⟨mk bas 0 v, hmk _ _ hv⟩
      rw [hform] at h1
      simpa [vCo_mk, uCo_mk, hv0] using h1
    have h2 : star ((A 0)ᵀ *ᵥ cst (uCo bas (x : Λ))) = (A 0)ᴴ *ᵥ cst (uCo bas (x : Λ)) := by
      funext i
      simp [cst, mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum]
    rw [hper, hv0, cst_zero, mulVec_zero, add_zero, h2]
    simp only [chartQ]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ ((A 0)ᴴ)⁻¹,
      Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mulVec]
    have h3 := hkerG _ hu
    have h4 : (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) *ᵥ
        cst (uCo bas (x : Λ)) = 0 := h3
    rw [h4, mulVec_zero]
  · set y : Fin g → ℂ := ((A 0)ᵀ)⁻¹ *ᵥ v with hy
    have hvy : (A 0)ᵀ *ᵥ y = v := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetT, Matrix.one_mulVec]
    obtain ⟨f1, -, f3⟩ := GlobalTheory.T.riemann_form_hermitian_lattice g (∑ j, B j) (T0 0) _ c h.c_pos hSPSD hτ hlow hGCh hrel
      hkerG y
    have hval : v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v =
        y ⬝ᵥ (compInv Pr ((T0 0).map Complex.im)).map (fun x : ℝ => (x : ℂ)) *ᵥ star y := by
      rw [← hconj, hvy]
    rw [hval]
    refine ⟨f1, fun h0 => ?_⟩
    have h1 := f3 h0
    rw [← hvy]
    have h2 := Submodule.mem_map_of_mem (f := ((A 0)ᵀ).mulVecLin) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨⟨mk bas u 0, hmk u 0 (by simp)⟩, fun x' => hrad u hu x', ?_⟩
    rw [hper]
    simp only [uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm
