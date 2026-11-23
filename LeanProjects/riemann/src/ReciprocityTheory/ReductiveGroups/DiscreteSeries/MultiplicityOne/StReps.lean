import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 RepsA

theorem stReps (h : UnitaryGroupStructuralFacts) : StReps := by
  obtain ⟨hB2, -, hRC, hBCF, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClG, -, hClW, -⟩ := hB2
  intro k r Wp _ _ _ D X hD _ γ hγ c d hc hd
  have hk := D.k_pos
  obtain ⟨hγu, hγz⟩ := hγ
  have hT : 0 < Tz k r D.z := D.T_pos

  have hdet : IsUnit γ.det := by
    have h1 := congrArg Matrix.det hγu
    rw [det_mul, det_mul, det_conjTranspose] at h1
    have hHb : (Hb k).det = -1 := by
      unfold Hb; rw [det_diagonal, Finset.prod_ite_eq' Finset.univ (Fin.last k) (fun _ => (-1 : ℂ))]
      simp
    rw [hHb] at h1
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0] at h1; simp at h1
  have hγi : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hdet
  have hγi' : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hdet
  have hHbi : (γ⁻¹)ᴴ * Hb k * γ⁻¹ = Hb k := by
    calc (γ⁻¹)ᴴ * Hb k * γ⁻¹ = (γ⁻¹)ᴴ * (γᴴ * Hb k * γ) * γ⁻¹ := by rw [hγu]
      _ = (γ * γ⁻¹)ᴴ * Hb k * (γ * γ⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hb k := by rw [hγi']; simp
  set μ := mud k d with hμ
  set M := γ * μ * γ⁻¹ with hM
  have hμu : μᴴ * Hb k * μ = Hb k := mud_unitary hk d hd

  have h1 : Mᴴ * Hb k * M = Hb k := by
    rw [show Mᴴ * Hb k * M = (γ⁻¹)ᴴ * (μᴴ * (γᴴ * Hb k * γ) * μ) * γ⁻¹ by
      simp only [hM, conjTranspose_mul, Matrix.mul_assoc]]
    rw [hγu, hμu, hHbi]

  set s : ℝ := Real.sqrt (Tz k r D.z) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hT).ne'
  have hzE : D.z = wbE k r ((s : ℂ) • (γ *ᵥ Pi.single (Fin.last k) 1)) := by
    rw [wbE_smul, ← embWb_mulVec, ← bvec_wI, hγz, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0,
      Complex.ofReal_one, one_smul]
  have hMγ : M * γ = γ * μ := by rw [hM, Matrix.mul_assoc, hγi, Matrix.mul_one]
  have h2 : herm (Hpk k r) (embWb k r M *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d := by
    conv_lhs => rw [hzE]
    rw [embWb_mulVec, herm_wbE, mulVec_smul, mulVec_mulVec, hMγ, ← mulVec_mulVec, herm_smul, herm_mulVec, hγu,
      herm_mud_last hk d, Complex.conj_ofReal, ← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
    ring

  have hB1 : bigCell k r c 1 ∈ GV k r := bigCell_one_unitary c hc
  have hEM : embWb k r M ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨M, h1, rfl⟩
  have hg0 : g0 k r γ c d = bigCell k r c 1 * embWb k r M := (hBCF k r c M).1
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [hg0]; exact (hClG k r).mul_mem _ hB1 _ hEM.1
  · set Γ := embWb k r γ with hΓdef
    set Γi := embWb k r γ⁻¹ with hΓidef
    have hΓΓi : Γ * Γi = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi', embWb_one]
    have hΓiΓ : Γi * Γ = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi, embWb_one]
    have hΓinv : Γ⁻¹ = Γi := inv_eq_right_inv hΓΓi
    have hΓW : Γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγu, rfl⟩
    have hΓiW : Γi ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ⁻¹, hHbi, rfl⟩
    have hconjM : ∀ N, embWb k r (γ * N * γ⁻¹) = Γ * embWb k r N * Γi := by
      intro N; rw [embWb_mul, embWb_mul]
    have e1 : Γi * g0 k r γ c d * Γ = bigCell k r c μ := by
      rw [hg0, hM, hconjM, (hBCF k r c μ).1]
      rw [show Γi * (bigCell k r c 1 * (Γ * embWb k r μ * Γi)) * Γ =
          (Γi * bigCell k r c 1) * Γ * embWb k r μ * (Γi * Γ) by simp only [Matrix.mul_assoc]]
      rw [(hUWb k r).2.2 c Γi hΓiW, Matrix.mul_assoc (bigCell k r c 1) Γi Γ, hΓiΓ, Matrix.mul_one, Matrix.mul_one]
    have e2 : gbar k r γ (g0 k r γ c d) =
        bigCell k r (star c) 1 * embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) := by
      unfold gbar
      rw [hΓinv, e1, bigCell_map_conj, (hBCF k r (star c) _).1, hconjM, ← Matrix.mul_assoc Γ,
        (hUWb k r).2.2 (star c) Γ hΓW]
      simp only [Matrix.mul_assoc]
    have hB1' : bigCell k r (star c) 1 * bigCell k r c 1 = 1 := bigCell_star_mul c hc
    have hμc : μ.map (starRingEnd ℂ) * μ = 1 := mud_conj_mul hk d hd
    have hE : embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) * embWb k r M = 1 := by
      rw [← embWb_mul, hM, show γ * μ.map (starRingEnd ℂ) * γ⁻¹ * (γ * μ * γ⁻¹) =
          γ * (μ.map (starRingEnd ℂ) * μ) * γ⁻¹ by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc γ⁻¹ γ, hγi, Matrix.one_mul],
        hμc, Matrix.mul_one, hγi', embWb_one]
    have hg0' : g0 k r γ c d = embWb k r M * bigCell k r c 1 := (hBCF k r c M).2
    unfold th
    rw [e2, Matrix.mul_inv_rev, inv_eq_right_inv hE, inv_eq_right_inv hB1', hg0']
  · have hz' : D.z' = D.z := hD.z_eq
    have hcond : Tz k r D.z * Tz k r D.z' <
        Complex.normSq (herm (Hpk k r) (embWb k r M *ᵥ D.z') D.z) := by
      rw [hz', h2, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
      have h1d : 1 < Complex.normSq d := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg d]
      have hTT : 0 < Tz k r D.z * Tz k r D.z := mul_pos hT hT
      nlinarith
    obtain ⟨h, hh, h', hh', hm⟩ :=
      hRC k r D.z D.z' D.μsec hk D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec (embWb k r M) hEM hcond
    rw [hz', h2] at hm
    rw [hz'] at hh'
    have hu := (hClW k r D.z).unit h hh
    have hu' := (hClW k r D.z).unit h' hh'
    refine ⟨h⁻¹, (hClW k r D.z).inv_mem h hh, h'⁻¹, (hClW k r D.z).inv_mem h' hh', ?_⟩
    rw [nonsing_inv_nonsing_inv h hu]
    show bigCell k r c (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * g0 k r γ c d * h'⁻¹
    have hE : embWb k r (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * embWb k r M * h'⁻¹ := by
      rw [hm]; simp only [← Matrix.mul_assoc]
      rw [mul_nonsing_inv h hu, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv h' hu', Matrix.mul_one]
    have hcm := (hUWb k r).2.2 c h ((hUWb k r).2.1 D.z hh)
    rw [(hBCF k r c _).1, hE, hg0]
    simp only [← Matrix.mul_assoc]
    rw [← hcm]

end ReciprocityTheory.ChartRestriction.DS.Mult1
