import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PiInvApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  let l : Fin (2 * r + k + 1) :=
    ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single l]
  · simp only [Hpk, l, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ l.val := fun h => hb (Fin.ext h)
    simp only [l, Fin.val_mk] at hb'
    have hbl := b.isLt
    apply mul_eq_zero_of_left
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hb' ⊢ <;> first | (exfalso; omega) | rfl
  · intro h
    exact absurd (Finset.mem_univ l) h

lemma uu_inv {z : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {u : Mat k r}
    (hu : u ∈ UUset k r z γ) : u⁻¹ ∈ UUset k r z γ := by
  simp only [UUset, UWset, UH, Set.mem_setOf_eq] at hu ⊢
  obtain ⟨⟨hH, hb, hz⟩, hw⟩ := hu
  have hdH : (Hpk k r).det ≠ 0 := by
    have h := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdu : IsUnit u.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hdH h.symm
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hdu
  have h3 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hdu
  have h2 : (u⁻¹)ᴴ * uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have fix : ∀ v, u *ᵥ v = v → u⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  refine ⟨⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩, fix _ hw⟩
  calc (u⁻¹)ᴴ * Hpk k r * u⁻¹ = (u⁻¹)ᴴ * (uᴴ * Hpk k r * u) * u⁻¹ := by rw [hH]
    _ = ((u⁻¹)ᴴ * uᴴ) * Hpk k r * (u * u⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

theorem core (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (hCI : ConjInv D) (hclW : IsClosed (UWset k r D.z))
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
    (hT6 : ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (hcomm : ∀ u ∈ UUset k r D.z γ, u * g0 = g0 * u)
    (f : Mat k r → ℂ) (hEf : ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS ≠ ∞) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = JF D (scalF Wp f) g0 := by
  have hz : D.z' = D.z := hD.z_eq
  have hπ : D.π' = D.π := hD.π_eq
  have Bc : ∀ F : Mat k r → (Wp →L[ℂ] Wp), ∀ u ∈ UUset k r D.z γ,
      (JF D F g0).comp (D.π u) = (D.π u).comp (JF D F g0) := by
    intro F u hu
    have hu' : u ∈ UWset k r D.z' := hz ▸ hu.1
    have e := J_equiv D hCI hu.1 hu' F g0
    have eg : u⁻¹ * g0 * u = g0 := by
      rw [Matrix.mul_assoc, ← hcomm u hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hu.1.1),
        Matrix.one_mul]
    rw [eg, Lab_apply, hπ] at e
    conv_lhs => rw [e]
    ext v
    simp only [ContinuousLinearMap.comp_apply, pi_inv_apply D hu.1]
  have hB : JF D (scalF Wp f) g0 = ∫ p, Phi D f g0 p ∂D.μSS := J_phi D hD f g0
  have hB' : JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS :=
    J_th D hD γ hE hgW hgN hlam hg0 f
  have hC := aesm_C D hD γ hclW hgW
  have hPC : ∀ᵐ p ∂D.μSS, Psi D γ f g0 p = (Phi D f g0 p).comp (Cf D γ p) ∧
      Phi D f g0 p = (Psi D γ f g0 p).comp (Cb D γ p) ∧ ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
    filter_upwards [ae_in D] with p hp using psi_eq_C D hD γ hWbar hp f g0
  by_cases hm : AEStronglyMeasurable (Phi D f g0) D.μSS
  swap
  · have hm' : ¬ AEStronglyMeasurable (Psi D γ f g0) D.μSS := fun h =>
      hm ((aesm_comp h hC.2).congr (hPC.mono fun p hp => hp.2.1.symm))
    rw [hB, hB', integral_non_aestronglyMeasurable hm, integral_non_aestronglyMeasurable hm']
  have hPhiI : Integrable (Phi D f g0) D.μSS := by
    refine ⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩
    have e : ∀ p, ‖Phi D f g0 p‖ₑ = ‖rho D p (scalF Wp f) g0‖ₑ := fun p => by
      have h1 : ‖ph D p‖ₑ = 1 := by
        rw [enorm_eq_nnnorm, show ‖ph D p‖₊ = 1 from NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact norm_ph D p),
          ENNReal.coe_one]
      rw [show Phi D f g0 p = ph D p • rho D p (scalF Wp f) g0 by rw [rho_scalF, hπ]; rfl, enorm_smul, h1, one_mul]
    calc ∫⁻ p, ‖Phi D f g0 p‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS := lintegral_congr e
      _ < ∞ := hEf.lt_top
  have hPsiM : AEStronglyMeasurable (Psi D γ f g0) D.μSS :=
    (aesm_comp hm hC.1).congr (hPC.mono fun p hp => hp.1.symm)
  have hPsiI : Integrable (Psi D γ f g0) D.μSS := by
    refine hPhiI.norm.mono' hPsiM (hPC.mono fun p hp => ?_)
    rw [hp.1]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp.2.2.1)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0 := ⟨_, rfl⟩
  have hYc : ∀ u ∈ UUset k r D.z γ, Y.comp (D.π u) = (D.π u).comp Y := fun u hu => by
    rw [hY, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, Bc _ u hu, Bc _ u hu]
  have key : ∀ᵐ p ∂D.μSS, trY Y (Psi D γ f g0 p) = trY Y (Phi D f g0 p) := by
    filter_upwards [ae_in D] with p hp
    have hh := hp.1
    have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hz ▸ hp.2.2.1
    have hy : Matrix.of p.1.1 * (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z := uw_mul hh (uw_inv hh')
    obtain ⟨u₀, hu₀, hth⟩ := hT6 _ hy
    have hop : (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹) =
        ((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1 : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
          (((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)).comp
            (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp)) := by
      rw [← D.π_rep.2 _ (hWbar _ hh') _ (uw_inv (hWbar _ hh)), ← th_mul_inv γ hE (isUnit_of_uh hh'.1), hth,
        D.π_rep.2 _ (uw_mul hu₀.1 hy) _ (uw_inv hu₀.1), D.π_rep.2 _ hu₀.1 _ hy, D.π_rep.2 _ hh _ (uw_inv hh')]
      ext v
      rfl
    have h2 : Y.comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) =
        (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp Y := by
      rw [← pi_inv_eq D hu₀.1]
      exact hYc _ (uu_inv hu₀)
    simp only [Psi, Phi, hop, map_smul, trY_conj Y _ _ h2]
  have hI1 : trY Y (∫ p, Psi D γ f g0 p ∂D.μSS) = trY Y (∫ p, Phi D f g0 p ∂D.μSS) := by
    rw [← ContinuousLinearMap.integral_comp_comm _ hPsiI, ← ContinuousLinearMap.integral_comp_comm _ hPhiI]
    exact integral_congr_ae key
  have hYY : trY Y (JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0) = 0 := by
    rw [map_sub, hB, hB', hI1, sub_self]
  rw [← hY] at hYY
  have h0 := trY_self hYY
  rwa [hY, sub_eq_zero] at h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

theorem stSym (hIn : UnitaryGroupStructuralFacts) : StSym := by
  intro k r Wp _ _ _ D X hD hX γ hγ f q _ hq hT hEf
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIall, -, -, -, -, -, -, -, -, hClW, -⟩, -, -, hBCF, hUWb, -⟩ := id hIn
  have hCI : ConjInv D := hCIall k r Wp Wp D
  obtain ⟨-, -, hW1, -, -, -, -, hμN, hμW⟩ := stInvGroup hIn k r Wp D X hD hX γ hγ
  have hChar := stInvChar k r Wp D X hD hX γ hγ
  have hL6 := stTransM hIn k r Wp D X hD hX γ hγ
  have hE : IsUnit (embWb k r γ).det := emb_unit (unit_of_frame hγ.1)
  have hTpos : 0 < Tz k r D.z := D.T_pos
  have hc : ∀ a, q.1 a ≠ 0 := by
    intro a ha0
    have hw : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hq
    unfold bcWeight at hw
    split_ifs at hw with h1
    · have hM : 0 < 2 * (Mdim k r a - 2) := by
        unfold Mdim
        have := a.isLt
        have := D.k_pos
        omega
      have h0 : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Mdim k r b - 2))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha0, norm_zero, zero_pow hM.ne'])
      rw [h0, zero_mul] at hw
      exact lt_irrefl _ hw
    · exact lt_irrefl _ hw
  have hT0 : ((Tz k r D.z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hTpos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = -(q.2 / ((Tz k r D.z : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hd : 1 < ‖d‖ := by
    have h3 : Tz k r D.z < ‖q.2‖ := by
      rw [Complex.normSq_eq_norm_sq] at hT
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg q.2]
    have hnT : ‖((Tz k r D.z : ℝ) : ℂ)‖ = Tz k r D.z := by
      rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]
    rw [hd_def, norm_neg, norm_div, hnT, one_lt_div hTpos]
    exact h3
  have hqd : (q.1, -((Tz k r D.z : ℝ) : ℂ) * d) = q := by
    refine Prod.ext rfl ?_
    show -((Tz k r D.z : ℝ) : ℂ) * d = q.2
    rw [hd_def]
    field_simp
  obtain ⟨-, -, -, hg0th, h₀, hh₀, h₀', hh₀', hgq⟩ := stReps hIn k r Wp D X hD hX γ hγ q.1 d hc hd
  rw [hqd] at hgq
  have hh₀'' : h₀' ∈ UWset k r D.z' := hD.z_eq ▸ hh₀'
  have red : ∀ F : Mat k r → (Wp →L[ℂ] Wp),
      JF D F (gq D q) = (Lab D hh₀ hh₀'').symm (JF D F (g0 k r γ q.1 d)) := fun F => by
    rw [J_equiv D hCI hh₀ hh₀'' F (g0 k r γ q.1 d), ← hgq, ContinuousLinearEquiv.symm_apply_apply]
  have hEf0 : ∫⁻ p, ‖rho D p (scalF Wp f) (g0 k r γ q.1 d)‖ₑ ∂D.μSS ≠ ∞ := by
    rw [E_equiv D hCI hh₀ hh₀'', ← hgq]
    exact hEf
  rw [red, red, core D hD hCI (hClW k r D.z).closed γ hE hμW hμN (fun m hm => (hChar m hm).1) hW1 hL6 hg0th
    (fun u hu => big_cell_commute_frame_element hBCF hUWb D.k_pos hγ hu q.1 d) f hEf0]

end ReciprocityTheory.ChartRestriction.DS.Mult1
