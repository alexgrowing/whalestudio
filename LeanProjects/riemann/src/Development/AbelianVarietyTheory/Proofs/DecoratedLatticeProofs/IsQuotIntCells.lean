import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.CellQuotInt

theorem isQuotInt_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ J hJ f hfJ hfR T hT
  classical
  obtain ⟨bX, lX, sX, -, -, -, hXH, hXR⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -, -, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  obtain ⟨hN, -, hH, hRi, hconj⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p hp hpc ν
  haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μX.IsMulRightInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]
    infer_instance
  have hRm : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p :=
    fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)
  have hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) :=
    (GlobalTheory.QuotInt.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let S : GL (n ⊕ Fin c) k → Set (GL n k × N k n c p) :=
    fun h => {z | h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J}
  have hSo : ∀ h, IsOpen (S h) := fun h =>
    hJ.1.preimage ((continuous_const.mul hm).mul continuous_const)
  have hScomp : ∀ h, ∃ D, IsCompact D ∧ S h ⊆ D := by
    intro h
    have hK : IsCompact ((fun x => h * x * h⁻¹) '' (J : Set (GL (n ⊕ Fin c) k))) :=
      hJ.2.image (by fun_prop)
    obtain ⟨D, hD, hDm⟩ := GlobalTheory.QuotInt.compact_preimage hN hK
    exact ⟨D, hD, fun z hz => hDm z ⟨_, hz, by group⟩⟩
  have hvol : ∀ h, volCell ν μX p J h = (μX.prod (volN ν n c p)) (S h) := by
    intro h
    rw [Measure.prod_apply (hSo h).measurableSet]
    rfl
  have hvol0 : ∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤ := by
    intro h
    obtain ⟨D, hD, hSD⟩ := hScomp h
    rw [hvol]
    exact ⟨(hSo h).measure_ne_zero _ ⟨(1, 1), by simp [S, J.one_mem]⟩,
      ((measure_mono hSD).trans_lt hD.measure_lt_top).ne⟩

  have hcell : ∀ h, ∫ g, (∫ u : N k n c p, (if h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0)
      ∂(volN ν n c p)) ∂μX = (((volCell ν μX p J h).toReal : ℝ) : ℂ) := by
    intro h
    have e : (fun z : GL n k × N k n c p =>
        if h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0) =
        (S h).indicator (fun _ => (1 : ℂ)) := by
      funext z
      simp [S, Set.indicator_apply]
    have hint : Integrable ((S h).indicator (fun _ => (1 : ℂ))) (μX.prod (volN ν n c p)) := by
      rw [integrable_indicator_iff (hSo h).measurableSet]
      exact integrableOn_const (by rw [← hvol]; exact (hvol0 h).2)
    rw [← e] at hint
    have h2 := integral_prod _ hint
    simp only at h2
    rw [← h2, e, integral_indicator_const _ (hSo h).measurableSet, Measure.real, ← hvol]
    simp
  have hmod : ∀ (φ : GL (n ⊕ Fin c) k → ℂ) (g₀ : GL n k) (u₁ : GL (n ⊕ Fin c) k), u₁ ∈ N k n c p →
      ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p)) ∂μX
        = ((nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) *
          ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX := by
    intro φ g₀ u₁ hu₁
    have hpos : ∀ y : kˣ, 0 < nabs k y := fun y => (nabs_properties k).2.1 y
    have e3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^ (-((c : ℝ) + 1 - 2 * p)) =
        nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) := by
      have h3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
        simp [nabs]
      rw [h3, Real.inv_rpow (hpos _).le, ← Real.rpow_neg (hpos _).le, neg_neg]
    have step : ∀ g : GL n k,
        ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p)) •
            ∫ u : N k n c p, φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p) := by
      intro g
      have e1 := hconj g₀⁻¹ (fun y => φ (embX c (g * g₀) * y * u₁))
      have e2 := integral_mul_right_eq_self (μ := volN ν n c p)
        (fun u : N k n c p => φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k))) ⟨u₁, hu₁⟩
      simp only [Subgroup.coe_mul, ← mul_assoc] at e2
      rw [e3, e2] at e1
      rw [← e1]
      congr 1
      funext u
      congr 1
      simp only [map_mul, map_inv]
      group
    simp only [step]
    rw [integral_smul, Complex.real_smul]
    congr 1
    have := integral_mul_right_eq_self (μ := μX)
      (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) g₀
    simpa using this

  have hv0 : ∀ h, (volCell ν μX p J h).toReal ≠ 0 := fun h =>
    ENNReal.toReal_ne_zero.2 (hvol0 h)
  let F : GL (n ⊕ Fin c) k → ℂ := fun x =>
    ∑ t ∈ T, if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0
  have hFsb : F ∈ SB (GL (n ⊕ Fin c) k) := by
    have := GlobalTheory.QuotInt.sb_of_quot J hJ.1 hJ.2 (T.image (QuotientGroup.mk : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k ⧸ J))
      (fun q => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = q then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0)
      (fun q hq => Finset.sum_eq_zero fun t ht => if_neg fun e => hq (Finset.mem_image.2 ⟨t, ht, e⟩))
    have hFeq : F = fun x : GL (n ⊕ Fin c) k => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = (x : GL (n ⊕ Fin c) k ⧸ J) then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0 := by
      funext x
      simp only [F, QuotientGroup.eq]
    rw [hFeq]
    exact this
  have hFint : ∫ x, F x ∂μG =
      ∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
    have hind : ∀ t : GL (n ⊕ Fin c) k,
        Integrable (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) μG ∧
        ∫ x, (if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) ∂μG =
          ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
      intro t
      have e : (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) =
          fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) (t⁻¹ * x) := by
        funext x
        simp [Set.indicator_apply]
      have hi : Integrable ((J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ))) μG := by
        rw [integrable_indicator_iff hJ.1.measurableSet]
        exact integrableOn_const hJ.2.measure_lt_top.ne
      rw [e]
      refine ⟨hi.comp_mul_left t⁻¹, ?_⟩
      rw [integral_mul_left_eq_self (fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) x) t⁻¹,
        integral_indicator_const _ hJ.1.measurableSet]
      simp only [Measure.real, Complex.real_smul]
      have := hv0 t
      push_cast
      field_simp
    show ∫ x, (∑ t ∈ T, _) ∂μG = _
    rw [integral_finset_sum _ (fun t _ => (hind t).1)]
    exact Finset.sum_congr rfl fun t _ => (hind t).2

  have hRinv : ∀ (y t : GL (n ⊕ Fin c) k), t⁻¹ * y ∈ J →
      DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t := by
    intro y t hy
    rw [DoubleCoset.eq]
    exact ⟨1, one_mem _, (t⁻¹ * y)⁻¹, J.inv_mem hy, by group⟩
  have hmkR : ∀ r ∈ R k n c p, ∀ y,
      DoubleCoset.mk (R k n c p) J (r * y) = DoubleCoset.mk (R k n c p) J y := by
    intro r hr y
    rw [DoubleCoset.eq]
    exact ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩
  have hFcell : ∀ t₀ ∈ T, ∀ y, DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t₀ →
      F y = if t₀⁻¹ * y ∈ J then f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) else 0 := by
    intro t₀ ht₀ y hy
    show (∑ t ∈ T, _) = _
    rw [Finset.sum_eq_single t₀]
    · intro t ht hne
      rw [if_neg]
      intro hmem
      exact hne (hT.1 (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht₀) ((hRinv y t hmem).symm.trans hy))
    · intro h
      exact absurd ht₀ h
  have hFoff : ∀ y, (∀ t ∈ T, DoubleCoset.mk (R k n c p) J y ≠ DoubleCoset.mk (R k n c p) J t) → F y = 0 := by
    intro y hy
    exact Finset.sum_eq_zero fun t ht => if_neg fun hmem => hy t ht (hRinv y t hmem)
  have havg : ∀ x, f x = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * x)
      ∂(volN ν n c p)) ∂μX := by
    intro x
    by_cases hx : ∃ t ∈ T, DoubleCoset.mk (R k n c p) J x = DoubleCoset.mk (R k n c p) J t
    · obtain ⟨t₀, ht₀, hxt⟩ := hx
      obtain ⟨r, hr, j, hj, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 hxt.symm
      obtain ⟨g₀, u₁, hu₁, rfl⟩ := Radical.exists_of_mem_R hr
      set φ : GL (n ⊕ Fin c) k → ℂ := fun y => f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) *
              (if t₀⁻¹ * y * t₀ ∈ J then (1 : ℂ) else 0) with hφ
      have key : ∀ (g : GL n k) (u : N k n c p),
          F (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j)) =
            φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) := by
        intro g u
        have hw : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁) ∈ R k n c p :=
          mul_mem (hRm g u) hr
        have e : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j) =
            (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        have hmk : DoubleCoset.mk (R k n c p) J
            ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            DoubleCoset.mk (R k n c p) J t₀ := by
          rw [DoubleCoset.eq]
          exact ⟨_, inv_mem hw, j⁻¹, J.inv_mem hj, by group⟩
        rw [e, hFcell t₀ ht₀ _ hmk]
        have e2 : t₀⁻¹ * ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            t₀⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        simp only [hφ, e2, J.mul_mem_cancel_right hj]
        split_ifs <;> simp
      simp only [key]
      rw [hmod φ g₀ u₁ hu₁]
      simp only [hφ, integral_const_mul]
      rw [hcell t₀, hfJ _ j hj, hfR g₀ u₁ hu₁ t₀]
      rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 (hv0 t₀))]
    · have hf0 : f x = 0 := by
        by_contra h0
        exact hx (hT.2 x h0)
      rw [hf0]
      have : ∀ (g : GL n k) (u : N k n c p), F (embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        apply hFoff
        intro t ht e
        exact hx ⟨t, ht, (hmkR _ (hRm g u) x).symm.trans e⟩
      simp [this]
  have hz₀ : IsQuotInt ν μX μG p f
      (∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t) :=
    ⟨F, hFsb, havg, hFint.symm⟩
  have huniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).1
  exact ⟨hvol0, fun z => ⟨fun hz => huniq _ _ hz hz₀, fun e => by rw [e]; exact hz₀⟩⟩

end GlobalTheory.CellQuotInt
