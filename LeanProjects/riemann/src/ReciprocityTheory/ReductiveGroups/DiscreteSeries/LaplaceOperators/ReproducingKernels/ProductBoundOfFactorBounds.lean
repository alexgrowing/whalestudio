import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.HpkMulVecMulVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec

open Formalism.QuantumDeterminants

theorem one_le_gN (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g :=
  DecA.one_le_gN' hg

theorem gN_inv (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN g⁻¹ = Formalism.FourierDecayAlt.B.gN g :=
  DecA.gN_inv' hg

theorem gN_mul_le (k r : ℕ) (a b : Mat k r) : Formalism.FourierDecayAlt.B.gN (a * b) ≤ Formalism.FourierDecayAlt.B.gN a * Formalism.FourierDecayAlt.B.gN b :=
  DecA.gN_mul_le' a b

theorem pair_bound (k r : ℕ) (a : ℝ) (ha : 0 ≤ a) (y g : Mat k r) (hy : y ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN g ^ (-a) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-a) ≤
      Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * (Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) + Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2))) := by
  have hA := DecA.one_le_gN' hg
  have hB := DecA.one_le_gN' (DecA.mul_mem hy hg)
  have hY := DecA.one_le_gN' hy
  have hYBA := DecA.gN_le_mul (y := y) hg
  have hAh : 0 ≤ Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hYq : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN (y * g)) with h | h
  · calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) :=
          DecA.pb_real a _ _ _ ha hA hB (by linarith) hYBA h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hYq
  · have := DecA.pb_real a (Formalism.FourierDecayAlt.B.gN (y * g)) (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN y) ha hB hA (by linarith)
      (by rw [mul_comm]; exact hYBA) h
    rw [mul_comm] at this
    calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hYq

theorem of_cont (k r : ℕ) : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) :=
  continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; exact (continuous_apply j).comp (continuous_apply i)

theorem gN_cont (k r : ℕ) : Continuous (fun M : Mat k r => Formalism.FourierDecayAlt.B.gN M) := by
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

theorem lmulM_cont {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

theorem conv_bound (k r : ℕ) (μG : Measure (Mt k r)) (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG)
    (a : ℝ) (ha : 0 ≤ a)
    (hI : Integrable (fun g : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2))) μG)
    (y : Mat k r) (hy : y ∈ UH (Hpk k r)) :
    ∫⁻ g : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-a) * Formalism.FourierDecayAlt.B.gN (y * Matrix.of g) ^ (-a)) ∂μG ≤
      ENNReal.ofReal (2 * (∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) *
        Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4))) := by
  have hGae : ∀ᵐ g ∂μG, Matrix.of g ∈ UH (Hpk k r) := ae_iff.2 hG.2.2.1
  have hm : Measurable (fun g : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2))) :=
    ((gN_cont k r).comp (of_cont k r)).measurable.pow_const _
  have hI0 : 0 ≤ ∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG :=
    integral_nonneg fun g => Real.rpow_nonneg (DecA.gN_nonneg _) _
  have h1 : ∫⁻ g : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2))) ∂μG =
      ENNReal.ofReal (∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) :=
    (ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun g => Real.rpow_nonneg (DecA.gN_nonneg _) _)).symm
  have h2 : ∫⁻ g : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (y * Matrix.of g) ^ (-(a / 2))) ∂μG =
      ENNReal.ofReal (∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) := by
    rw [← h1]
    conv_rhs => rw [← hG.2.2.2 y hy]
    rw [lintegral_map hm.ennreal_ofReal (lmulM_cont y).measurable]
    rfl
  have hY0 : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) := Real.rpow_nonneg (DecA.gN_nonneg _) _
  calc _ ≤ ∫⁻ g : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4))) *
          (ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2))) +
            ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (y * Matrix.of g) ^ (-(a / 2)))) ∂μG := by
        refine lintegral_mono_ae (hGae.mono fun g hg => ?_)
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg (DecA.gN_nonneg _) _) (Real.rpow_nonneg (DecA.gN_nonneg _) _),
          ← ENNReal.ofReal_mul hY0]
        exact ENNReal.ofReal_le_ofReal (pair_bound k r a ha y _ hy hg)
    _ = ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4))) *
          (ENNReal.ofReal (∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) +
            ENNReal.ofReal (∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm.ennreal_ofReal, h1, h2]
    _ = _ := by
        rw [← ENNReal.ofReal_add hI0 hI0, ← ENNReal.ofReal_mul hY0]; congr 1; ring

theorem UW_inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := DecA.inv_mul hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨DecA.inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem UH_closed (k r : ℕ) : IsClosed (UH (Hpk k r) : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem UW_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
      {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
    ext g; simp only [UWset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (UH_closed k r).inter ((isClosed_iInter fun a =>
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const))

theorem psiGen_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun M : Mat k r => Formalism.MainNotions.S.psiGen k r z c M) := by
  have hell : ∀ a : Fin r, Continuous (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) := by
    intro a
    by_cases h : a.val + 1 < r
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) =
          fun M : Mat k r => M (eI k r a) (eI k r ⟨a.val + 1, h⟩) :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_pos h]
      rw [e]; exact continuous_id.matrix_elem _ _
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) = fun M : Mat k r => ∑ j, M (eI k r a) j * z j :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_neg h]; rfl
      rw [e]; exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

theorem product_bound_of_factor_bounds (D M1 M2 X P Q C : ℝ) (hD : 0 ≤ D) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hX : 0 ≤ X)
    (h1 : M1 ≤ C * P) (h2 : M2 ≤ C * Q) : D * M1 * (M2 * X) ≤ D * C ^ 2 * X * (P * Q) := by
  have := mul_le_mul h1 h2 hM2 (hM1.trans h1)
  calc D * M1 * (M2 * X) = (D * X) * (M1 * M2) := by ring
    _ ≤ (D * X) * ((C * P) * (C * Q)) := mul_le_mul_of_nonneg_left this (mul_nonneg hD hX)
    _ = _ := by ring

def Sg3 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x₀ x : Mat k r) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧
    x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1 ∈ UH (Hpk k r))}

theorem joint_integrable (hIG : IntGStatement) (hIS : IntSStatement)
    (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d a C : ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (μG μW μN : Measure (Mt k r))
    (hσ : Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ) (hw : ‖w‖ = 1) (hF : IsFdegB μG σ d)
    (hdec : ∀ g ∈ UH (Hpk k r), ‖⟪w, σ g w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ha : 4 * max (bG k r) (bS k r) < a - 1)
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π)
    (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG) (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW)
    (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN)
    (x₀ : Mat k r) (hx₀ : x₀ ∈ UH (Hpk k r)) (ξ : Vp) (x : Mat k r) (hx : x ∈ UH (Hpk k r)) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.MainNotions.S.eFun μG σ w (Matrix.of q.1) •
        (⟪w, σ (x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1))) w⟫_ℂ •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ))
      (μG.prod (μW.prod μN)) := by
  have : SigmaFinite μG := hG.1
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hbG : 0 ≤ bG k r := by unfold bG nS q0S; positivity
  have hm1 := le_max_left (bG k r) (bS k r)
  have hm2 := le_max_right (bG k r) (bS k r)
  have ha0 : 0 ≤ a := by linarith
  have hI := hIG k r μG hG (a / 2) (by linarith)
  have hS := hIS k r z μW μN hz hT hW hN x₀ hx₀ x hx (a / 4) (by linarith)
  have hGae : ∀ᵐ g ∂μG, Matrix.of g ∈ UH (Hpk k r) := ae_iff.2 hG.2.2.1
  have hWae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := ae_iff.2 hW.2.2.1
  have hNae : ∀ᵐ m ∂μN, Matrix.of m ∈ Nset k r := ae_iff.2 hN.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ UH (Hpk k r) ∧
      (Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r) :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have hYmem : ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r →
      x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x) ∈ UH (Hpk k r) := fun p hp =>
    DecA.mul_mem (DecA.inv_mem hx₀) (DecA.mul_mem (DecA.mul_mem hp.1.1 hp.2.1) hx)
  have hof := of_cont k r
  have hof1 : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => Matrix.of q.1) := hof.comp continuous_fst
  have hof21 : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => Matrix.of q.2.1) :=
    hof.comp (continuous_fst.comp continuous_snd)
  have hof22 : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => Matrix.of q.2.2) :=
    hof.comp (continuous_snd.comp continuous_snd)
  have hYc : Continuous (fun q : Mt k r × (Mt k r × Mt k r) =>
      x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1) :=
    (continuous_const.matrix_mul ((hof21.matrix_mul hof22).matrix_mul continuous_const)).matrix_mul hof1

  have hΦm : Measurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-a) *
        Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1) ^ (-a)) :=
    (((gN_cont k r).comp hof1).measurable.pow_const _).mul (((gN_cont k r).comp hYc).measurable.pow_const _)
  have hΦ : Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-a) *
        Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1) ^ (-a))
      (μG.prod (μW.prod μN)) := by
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
      mul_nonneg (Real.rpow_nonneg (DecA.gN_nonneg _) _) (Real.rpow_nonneg (DecA.gN_nonneg _) _)),
      lintegral_prod_symm' _ hΦm.ennreal_ofReal]
    have hI0 : 0 ≤ 2 * ∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG :=
      mul_nonneg zero_le_two (integral_nonneg fun g => Real.rpow_nonneg (DecA.gN_nonneg _) _)
    calc _ ≤ ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (2 * ∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) *
            ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-(a / 4))) ∂(μW.prod μN) := by
          refine lintegral_mono_ae (hPae.mono fun p hp => ?_)
          dsimp only
          rw [← ENNReal.ofReal_mul hI0]
          exact conv_bound k r μG hG a ha0 hI _ (hYmem p hp)
      _ = ENNReal.ofReal (2 * ∫ g : Mt k r, Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-(a / 2)) ∂μG) *
            ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal
              (Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-(a / 4))) ∂(μW.prod μN) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.lintegral_lt_top

  have hScl : IsClosed (Sg3 k r z x₀ x) :=
    ((UH_closed k r).preimage hof1).inter (((UW_closed k r z).preimage hof21).inter ((UH_closed k r).preimage hYc))
  have hSae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ Sg3 k r z x₀ x := by
    filter_upwards [hQae] with q hq
    exact ⟨hq.1, hq.2.1, DecA.mul_mem (hYmem q.2 hq.2) hq.1⟩
  have hassoc : ∀ q : Mt k r × (Mt k r × Mt k r),
      x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1)) =
        x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1 := fun q => by
    simp only [Matrix.mul_assoc]
  have hE1 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => Formalism.MainNotions.S.eFun μG σ w (Matrix.of q.1)) (Sg3 k r z x₀ x) := by
    have h := (hσ.2.2 w).comp hof1.continuousOn (fun q (hq : q ∈ Sg3 k r z x₀ x) => hq.1)
    exact continuousOn_const.mul (continuous_star.comp_continuousOn (continuousOn_const.inner h))
  have hE2 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪w, σ (x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1))) w⟫_ℂ) (Sg3 k r z x₀ x) := by
    have hc : Continuous (fun q : Mt k r × (Mt k r × Mt k r) =>
        x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1))) :=
      continuous_const.matrix_mul ((hof21.matrix_mul hof22).matrix_mul (continuous_const.matrix_mul hof1))
    have h := (hσ.2.2 w).comp hc.continuousOn (fun q (hq : q ∈ Sg3 k r z x₀ x) => by
      show _ ∈ UH (Hpk k r)
      rw [hassoc q]; exact hq.2.2)
    exact continuousOn_const.inner h
  have hE3 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ) (Sg3 k r z x₀ x) := by
    show ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)) • π (Matrix.of q.2.1)⁻¹ ξ) (Sg3 k r z x₀ x)
    have hinvc : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1)⁻¹) (Sg3 k r z x₀ x) :=
      (((continuous_const.matrix_mul hof21.matrix_conjTranspose).matrix_mul continuous_const).continuousOn).congr
        (fun q (hq : q ∈ Sg3 k r z x₀ x) => DecA.inv_eq hq.2.1.1)
    have h := (hπ.2.2 ξ).comp hinvc (fun q (hq : q ∈ Sg3 k r z x₀ x) => UW_inv_mem hq.2.1)
    exact (continuous_star.comp ((psiGen_cont k r z c).comp hof22)).continuousOn.smul h
  refine Integrable.mono' (hΦ.const_mul (‖(Formalism.MainNotions.S.fdegH μG σ w : ℂ)‖ * C ^ 2 * ‖ξ‖)) ?_ ?_
  · rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact (hE1.smul (hE2.smul hE3)).aestronglyMeasurable hScl.measurableSet
  filter_upwards [hQae] with q hq
  have hyG := DecA.mul_mem (hYmem q.2 hq.2) hq.1
  have h1 := hdec _ hq.1
  have h2 := hdec _ hyG
  have hψ : ‖Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)‖ = 1 := by
    unfold Formalism.MainNotions.S.psiGen; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hπ' : ‖π (Matrix.of q.2.1)⁻¹ ξ‖ = ‖ξ‖ := hπ.2.1 _ (UW_inv_mem hq.2.1) ξ
  simp only [Formalism.MainNotions.S.eFun, chiInv, norm_smul, norm_mul, norm_star, hψ, hπ', hassoc q, one_mul]
  exact product_bound_of_factor_bounds _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) h1 h2

theorem repro_of_int (hIG : IntGStatement) (hIS : IntSStatement) : ReproStatement := by
  intro k r H _ _ _ σ w d a C Vp _ _ _ π z c μG μW μN hσ hw hF hdec ha hz hT hπ hG hW hN x₀ hx₀ ξ x hx
  exact Core.repro_core k r H σ w d Vp (Formalism.MainNotions.S.psiGen k r z c) π z μG μW μN x₀ x ξ hσ hw hF hG hW hN hx₀ hx
    (joint_integrable hIG hIS k r H σ w d a C Vp π z c μG μW μN hσ hw hF hdec ha hz hT hπ hG hW hN
      x₀ hx₀ ξ x hx)

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec
