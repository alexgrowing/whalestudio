import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroFdeg
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.BesselIntegralSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTopA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem psi_eq_PsiM {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ)
    (hF : ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
      Ψ (NormedSpace.exp X) =
        ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
          ∫ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ •
            (T.op k * S7.projW T * T.op k⁻¹) ∂(S7.muK ε)) :
    ∀ g ∈ UJset ε, Ψ g = S7.PsiM T μ g := by
  intro g hg
  have hex : ∃ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = S7.toMK k * NormedSpace.exp X :=
    S7.polar_exists hg
  have key : ∀ (kc : S7.KG ε) (Xc : Matrix (Fin n) (Fin n) ℂ), inP ε Xc → g = S7.toMK kc * NormedSpace.exp Xc →
      Ψ g = T.op kc * S7.psM T μ (NormedSpace.exp Xc) := by
    intro kc Xc hXc hgc
    have hu : inUJ ε (NormedSpace.exp Xc) := by
      have := S7.inUJ_kexp (1 : S7.KG ε) hXc
      rwa [pdA_toMK_one, Matrix.one_mul] at this
    have h1 := hK kc 1 (NormedSpace.exp Xc) hu
    rw [pdA_toMK_one, Matrix.mul_one, pdA_op_one, mul_one] at h1
    have hps : Ψ (NormedSpace.exp Xc) = S7.psM T μ (NormedSpace.exp Xc) := by
      rw [hF Xc hXc]
      simp only [szt_phiM_inv_conj μ hXc]
      rfl
    rw [hgc, h1, hps]
  unfold S7.PsiM
  rw [dif_pos hex]
  exact key _ _ hex.choose_spec.choose_spec.1 hex.choose_spec.choose_spec.2

theorem sigZero (hAll : ∀ m : ℕ, S7.PsiAllStatement m) : Lap.SigZeroStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hlamR, -, -, -, hGL⟩ := hS
  have hqOf : qOf (Formalism.MainNotions.CayleySignature.eps48 k r) = r + 1 := Lap.noncompactCount_parabolicSign k r hk
  have hpOf : pOf (Formalism.MainNotions.CayleySignature.eps48 k r) = k + r := by
    rw [Lap.compactCount_parabolicSign k r hk]; omega
  obtain ⟨P, hPc⟩ := exists_cayley_unitary k r hk
  generalize Formalism.MainNotions.CayleySignature.lam48 k r v b = lam at hlamR hGL ⊢
  generalize Formalism.MainNotions.CayleySignature.eps48 k r = ε at hqOf hpOf hPc hGL ⊢
  have hlam : S7.IsHCParam lam := (mir_isHCParam_iff lam).1 hlamR
  obtain ⟨hanti, hgapAt, hN⟩ := hGL

  have hq0 : S7.q0 ε = min (k + r) (r + 1) := by unfold S7.q0; rw [hpOf, hqOf]
  have hq1 : 1 ≤ S7.q0 ε := by rw [hq0]; exact le_min (by omega) (by omega)
  have hQ1 : (1 : ℝ) ≤ (S7.q0 ε : ℝ) := by exact_mod_cast hq1
  have hp' : (pOf ε : ℝ) = (k : ℝ) + r := by rw [hpOf, Nat.cast_add]
  have hq' : (qOf ε : ℝ) = (r : ℝ) + 1 := by rw [hqOf, Nat.cast_add, Nat.cast_one]
  have hmin : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; rw [Nat.cast_min]
  unfold Lap.hNeed at hN
  try simp only [Nat.cast_min] at hN
  rw [hmin, hp', hq'] at hN
  obtain ⟨hN1, hN2⟩ := max_lt_iff.1 hN
  obtain ⟨hN2a, hN2b⟩ := max_lt_iff.1 hN2
  have hN1' := lt_of_le_of_lt (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)) hN1
  obtain ⟨-, hNpq⟩ := max_lt_iff.1 hN1'
  have hNn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgap : StdGap ε lam := ⟨hanti, h, hgapAt, by rw [hp', hq']; linarith⟩
  have hNQ : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := mul_nonneg hNn (by linarith)
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have h8 : 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < h := by linarith
  have hthr : 4 * max (Lap.S0.bG k r) (Lap.S0.bS k r) < h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) - 1 := by
    have hbG : Lap.S0.bG k r = 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by
      unfold Lap.S0.bG Lap.S0.nS Lap.S0.q0S; rw [← hq0]
    have hbS : Lap.S0.bS k r = 2 * ((r : ℝ) + 1 - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
      unfold Lap.S0.bS Lap.S0.nS; ring
    rw [hbG, hbS]
    have hs : 0 < Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_pos.2 (by linarith)
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
    nlinarith [hN2b]

  have hint := hlam.2
  choose mm hmm using hint
  let μ : Fin (2 * r + k + 1) → ℤ := fun a => mm a + ((2 * r + k + 1 : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)
  have hμ : S7.IsMu lam μ := by
    unfold S7.IsMu
    intro a
    have ha := hmm a
    simp only [μ]
    unfold rho
    push_cast at ha ⊢
    linarith

  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, ha, hb, hc, hd, hdec, he, -, hF⟩ := hAll (2 * r + k + 1) ε lam h T hlam hgapAt hq1
  have hP : IsPsiFor ε lam T Ψ := ⟨ha, hb, hc, hd, fun μ' hμ' => (he μ' hμ').2.1 h8⟩
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hPsi := psi_eq_PsiM ha hμ (hF μ hμ)
  have hDS := isDS_sigLam hgap hP hv₀
  refine ⟨↥(Hlam ε Ψ T.w), inferInstance, inferInstance, inferInstance,
    fun g => sigLam ε Ψ T.w (P * g * P⁻¹), isDSHpk_of_isDS hPc hDS, isURepOn_UH_of hPc hDS.2.2.1, ?_⟩
  intro w₀ hw₀
  have hlow := isLowUnit_of_isLowUnitH hPc hDS hw₀
  have hlowK : Formalism.MainNotions.S.lowKSub ε lam (sigLam ε Ψ T.w) = lowKSubLam ε Ψ T.w := by
    obtain ⟨h1, h2⟩ := sigLam_lowK hgap hP hv₀
    unfold Formalism.MainNotions.S.lowKSub
    have hset : {S | Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) (Formalism.QuantumDeterminants.lowK ε lam) S} =
        {lowKSubLam ε Ψ T.w} :=
      Set.ext fun S => ⟨fun hS => h2 S hS, fun hS => by rw [Set.mem_singleton_iff.1 hS]; exact h1⟩
    rw [hset, sSup_singleton]
  have hmem : w₀ ∈ lowKSubLam ε Ψ T.w := hlowK ▸ hlow.2
  unfold lowKSubLam at hmem
  rw [Submodule.mem_comap, Submodule.mem_map] at hmem
  obtain ⟨x, hx, hxw⟩ := hmem
  obtain ⟨v₁, hv₁⟩ := (mem_datumV_iff hP T.w x).1 hx
  have hxw' : (x : L2 ε) = (w₀ : L2 ε) := hxw
  have hw0L : (w₀ : L2 ε) = uniformisationL2 ε Ψ T.w v₁ := by rw [← hv₁, hxw']
  have hw0 : w₀ = ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩ := Subtype.ext hw0L
  have hv1 : v₁ ≠ 0 := by
    intro h0
    have hj0 : uniformisationL2 ε Ψ T.w 0 = 0 := by simpa using datumEmbedding_smul hP T.w 0 0
    have hz : w₀ = 0 := Subtype.ext (by rw [hw0L, h0, hj0]; rfl)
    have h1 := hlow.1
    rw [hz, norm_zero] at h1
    exact zero_ne_one h1
  have hc1 : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 (datumEmbedding_highest_ne_zero hgap hP hv₀)))
  obtain ⟨C, hC⟩ := dec_gN_sigLam hgap hP hv₀ hq1 hdec v₁ v₁
  refine ⟨fun μG hμG => fdegB_of_isDS hPc hDS μG hμG,
    ⟨h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))), C, hthr, fun g hg => ?_⟩,
    T, μ, P, v₁, _, hv1, hc1, hμ, hPc.1, fun g hg => ?_⟩
  · have hgJ := szt_conj_mem hPc hg
    show ‖inner ℂ w₀ (sigLam ε Ψ T.w (P * g * P⁻¹) w₀)‖ ≤ _
    rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hgJ, hw0L]
    calc _ ≤ C * Real.sqrt (S7.hs (P * g * P⁻¹)) ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) :=
          hC _ hgJ
      _ = _ := by rw [szt_hs_conj hPc, szt_gN_eq]
  · have hgJ := szt_conj_mem hPc hg
    show inner ℂ w₀ (sigLam ε Ψ T.w (P * g * P⁻¹) w₀) = _
    rw [hw0, formulaF_sigLam hgap hP hv₀ hgJ v₁ v₁]
    unfold Lap.psiCoef
    rw [hPsi _ hgJ]
    rfl

end ReciprocityTheory.ChartRestriction.DS
