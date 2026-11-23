import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.PsiGenNorm

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def PiCont : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)), inWb k r z → 0 < Tz k r z →
    IsHCTypeW k r z u π → ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z)

theorem ellA_cont (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  unfold ellA
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => (continuous_id.matrix_elem _ j).mul continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul (ellA_cont z a)))))

theorem inv_contOn : ContinuousOn (fun h : Mat k r => h⁻¹) (Gr k r) := by
  unfold Gr
  have key : ∀ h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), h⁻¹ = (h.det)⁻¹ • h.adjugate := fun h _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ key
  exact ((continuous_id.matrix_det.continuousOn).inv₀
    (fun h hh => (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh).ne_zero)).smul continuous_id.matrix_adjugate.continuousOn

theorem ae_product_mem_unipotent_and_nilradical {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hUWG : UWset k r z ⊆ Gr k r) (hNG : Nset k r ⊆ Gr k r) :
    ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
      (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r) := by
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p
      simp
    rw [e, Measure.prod_prod, hW, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} = Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r} := by
      ext p
      simp
    rw [e, Measure.prod_prod, hN, mul_zero]
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨⟨hp1, hp2⟩, hp1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (hUWG hp1) (hNG hp2)⟩

section Meas

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem bInt_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {μW μN : Measure (Mt k r)}
    (hUWc : IsClosed (UWset k r z)) (hUWG : UWset k r z ⊆ Gr k r)
    (hUWinv : ∀ h ∈ UWset k r z, h⁻¹ ∈ UWset k r z)
    (hπc : ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z))
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (w' : H) (ξ : Vp) (v : H) : AEStronglyMeasurable (bInt z c σ π w' ξ v) (μW.prod μN) := by
  set T : Set (Mt k r × Mt k r) :=
    {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r} with hTdef
  have hfst : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r) := continuous_fst
  have hsnd : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r) := continuous_snd
  have hmul : Continuous fun p : Mt k r × Mt k r => Matrix.of p.1 * Matrix.of p.2 :=
    hfst.matrix_mul hsnd
  have hTc : IsClosed T := (hUWc.preimage hfst).inter (gr_isClosed.preimage hmul)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) v) T :=
    (hσ.2.2 v).comp hmul.continuousOn (fun p hp => hp.2)
  have hi : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1)⁻¹) T :=
    inv_contOn.comp hfst.continuousOn (fun p hp => hUWG hp.1)
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) T :=
    (hπc ξ).comp hi (fun p hp => hUWinv _ hp.1)
  have h3 : Continuous fun p : Mt k r × Mt k r => star (psiGen k r z c (Matrix.of p.2)) :=
    continuous_star.comp ((psiGen_cont z c).comp hsnd)
  have hcont : ContinuousOn (bInt z c σ π w' ξ v) T :=
    ((continuousOn_const.inner h1).mul h3.continuousOn).smul h2
  have := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
  have hae' : ∀ᵐ p ∂(μW.prod μN), p ∈ T := hae
  rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this

end Meas

theorem aInt_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : AInt := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g hg
  obtain ⟨C, _, hCb⟩ := aBound_of hSG hD hRG hS hPi hNI hU k r z c u v b H σ Vp π w μG μS ν μW μN
    hH hR hC x₀ hx₀ ξ
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, _, _⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have := hμW.1
  have := hμN.1
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  refine ⟨bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG (fun h hh => (hUW h hh h hh).2.1)
    (hPC k r z u Vp π hz hT hHC) (hae.mono fun p hp => hp.2) _ _ _, ?_⟩
  exact (hCb g hg).trans_lt ENNReal.ofReal_lt_top

theorem aCont_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : ACont := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g₀ hg₀
  have : FirstCountableTopology (Mat k r) :=
    inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨Cφ, hCφ0, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hC x₀ hx₀
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, hWfin, hNc⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have hPU := (hPi k r z u Vp π hz hT hHC).2
  obtain ⟨Kw, hKw⟩ := (hU k r z hz hT).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  have hKw0 : 0 ≤ max Kw 0 := le_max_right _ _
  have hinvb : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ max Kw 0 := fun h hh =>
    le_max_of_le_left ((Real.le_norm_self _).trans (hKw _ (hUW h hh h hh).2.1))
  have := hμW.1
  have := hμN.1
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  have hH2 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  set K0 := Cφ * (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r * ‖ξ‖
    with hK0d
  have hK0 : 0 ≤ K0 := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0
    (mul_nonneg hH2 (by linarith [opn_nonneg g₀]))) _)) (norm_nonneg _)
  have hmeas : Measurable fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r) :=
    (show Continuous fun m : Mt k r => opn (Matrix.of m) from opn_continuous).measurable.pow_const _
  have hgi : Integrable (fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r)) μN := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun m =>
      Real.rpow_nonneg (opn_nonneg _) _)]
    exact hNI k r μN hμN hNc
  have hbi : Integrable (fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
      (μW.prod μN) := by
    have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hgi
    simpa using this.const_mul K0
  show ContinuousWithinAt (fun g => ∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
    (Gr k r) g₀
  apply continuousWithinAt_of_dominated
    (bound := fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
  · exact Filter.Eventually.of_forall fun g => bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG
      (fun h hh => (hUW h hh h hh).2.1) (hPC k r z u Vp π hz hT hHC)
      (hae.mono fun p hp => hp.2) _ _ _
  · have hev1 : ∀ᶠ g in 𝓝[Gr k r] g₀, g ∈ Gr k r := self_mem_nhdsWithin
    have hev2 : ∀ᶠ g in 𝓝[Gr k r] g₀, opn g < opn g₀ + 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((opn_continuous (k := k) (r := r)).continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
    filter_upwards [hev1, hev2] with g hg hlt
    filter_upwards [hae] with p hp
    refine (bInt_bound z c hσ (π := π) hCφ hKw0 ξ p (hUWG hp.1.1) (hinvb _ hp.1.1)
      (hPU _ (hUW _ hp.1.1 _ hp.1.1).2.1 ξ) (hNG hp.1.2) hg).trans ?_
    have hle : (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r ≤
        (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r :=
      Real.rpow_le_rpow (mul_nonneg hKw0 (mul_nonneg hH2 (opn_nonneg _)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt.le hH2) hKw0) hN
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle hCφ0) (norm_nonneg _)) (Real.rpow_nonneg (opn_nonneg _) _)
  · exact hbi
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : ContinuousWithinAt (fun g => σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)) (Gr k r) g₀ :=
      (σ _).continuous.continuousAt.comp_continuousWithinAt (hσ.2.2 w g₀ hg₀)
    exact ((continuousWithinAt_const.inner h1).mul continuousWithinAt_const).smul
      continuousWithinAt_const

end WlocSk.PtD
