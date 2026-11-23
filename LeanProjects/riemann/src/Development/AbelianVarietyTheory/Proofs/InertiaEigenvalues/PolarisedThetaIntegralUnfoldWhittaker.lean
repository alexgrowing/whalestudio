import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransformStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariantStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem lastRow_uGL_mul (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GroundTheory.Automorphic.FourierWhittaker.uGL X * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GroundTheory.Automorphic.FourierWhittaker.coe_uGL, Matrix.mul_apply,
    GroundTheory.Automorphic.FourierWhittaker.uMat_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), dif_neg (not_lt.2 (Fin.le_last c)), zero_mul]
  · simp

theorem jswWhit_fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) :
    GlobalTheory.JSW.whit (fT φ Φ) g = sqrtC Φ (yInf g) * GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv (yInf g))) := by
  simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [fT_of_lastRow (lastRow_uGL_mul X g), mul_assoc (GroundTheory.Automorphic.FourierWhittaker.uGL X) g]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem indN_eq_re (N : ℕ) (y : Fin (m + 1) → Af E) : indN N y = ((indN N y).re : ℂ) := by
  unfold indN; split_ifs <;> simp

theorem indN_re_nonneg (N : ℕ) (y : Fin (m + 1) → Af E) : 0 ≤ (indN N y).re := by
  unfold indN; split_ifs <;> simp

theorem wt_coe (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    (((wt N x g : ℝ≥0) : ℝ) : ℂ) = indN N (yFin g) * (detPow E (m + 1) x g : ℂ) := by
  have h0 : 0 ≤ detPow E (m + 1) x g := norm_nonneg _
  rw [wt, Real.coe_toNNReal _ (mul_nonneg (indN_re_nonneg N _) h0), Complex.ofReal_mul, ← indN_eq_re]

theorem sqrtC_mul_conj {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (u : Fin (m + 1) → Cinf E) :
    sqrtC Φ u * conj (sqrtC Φ u) = Φ u := by
  rw [sqrtC, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hΦ u).1]
  exact Complex.ext (by simp) (by simp [(hΦ u).2])

theorem psi_lastRow_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) =
      fT φ Φ g * conj (fT φ' Φ g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, fT, fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change φ (g * (infGL E (m + 1)) (secInv (yInf g))) * conj (φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem uInt_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ' Φ N x g =
      GlobalTheory.JSW.whit (fT φ Φ) g * conj (GlobalTheory.JSW.whit (fT φ' Φ) g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, jswWhit_fT, jswWhit_fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change GlobalTheory.JSW.whit φ (g * (infGL E (m + 1)) (secInv (yInf g))) *
    conj (GlobalTheory.JSW.whit φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

omit [IsTotallyComplex E] in

theorem NE_eq_ratMirU_zero : GlobalTheory.CellDec.NE E (m + 1) = ratMirU E (m + 1) 0 := by
  have h : GlobalTheory.SmGL.unipB E (Fin (m + 1)) = mirU E (m + 1) 0 := by
    ext γ
    rw [GlobalTheory.SmGL.mem_unipB, mem_mirU_zero]
  rw [GlobalTheory.CellDec.NE, ratMirU, h]

omit [IsTotallyComplex E] in
theorem isMir_of_mem_mirU_zero {γ : GL (Fin (m + 1)) E} (hγ : γ ∈ mirU E (m + 1) 0) : IsMir m γ := by
  intro i k h
  refine hγ i k (Nat.zero_le _) ?_
  rcases h with h | h
  · have := k.2; change (k : ℕ) ≤ i; omega
  · have := k.2; omega

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

theorem enorm_uInt_self {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ = ‖GlobalTheory.JSW.whit (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) := by
  rw [uInt_eq hΦ, enorm_mul, enorm_mul, RCLike.enorm_conj, pow_two]
  congr 1
  have h0 : (((wt N x g : ℝ≥0) : ℝ) : ℂ) = ((wt N x g : ℝ≥0) : ℂ) := rfl
  rw [h0, enorm_eq_nnnorm]
  congr 1
  ext
  simp

theorem zint_unfold : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  rw [GlobalTheory.T.rankinSelbergThetaIntegral_unfold_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin, e2,
    Complex.ofReal_one, one_mul, e1]
  exact hEq

end GlobalTheory.ZUnf
