import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuousStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsShiftedVectorShintaniFormulaRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariantStatement

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSCell

theorem exists_isUnifV : ∀ (E : Type) [Field E] [NumberField E], ∃ ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ, ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E) := by
  intro E _ _
  refine ⟨fun w => GroundTheory.Global.uniformizerUnit w, fun w => ?_⟩
  have h := GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  rw [zpow_one] at h
  exact h

set_option maxHeartbeats 4000000 in

theorem lintegral_unfolded_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, π₀, ω, hα, hmk, hωu, hω, hπ₀, hsat⟩ := GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary E (m + 1) π hπ T hT
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E
  obtain ⟨F, hF, l₀, hl₀, ⟨U, hUo, hU⟩, hK, hW0, ⟨C, hC, hCp⟩, hprof⟩ := GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified E m T π₀ hπ₀ α hsat ϖ hϖ
  have hSm : F ∈ Sm E (m + 1) := (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ₀ hF : GlobalTheory.MSpanDecay.Good F).mem_Sm
  let φ : Sm E (m + 1) := ⟨F, hSm⟩
  have hFc : Continuous F := by
    refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E (m + 1) φ
      (GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun k hk => ?_))
    exact Subtype.ext (funext fun g => hU k hk g)
  obtain ⟨hWc, hWN⟩ := GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant E (m + 1) F hFc (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant E (m + 1) π₀ F hF)
  obtain ⟨Φ, J, hΦs, hΦc, hΦr, hΦreal, hΦ1, hJ0, horb⟩ := GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit E (m + 1) (Fin.last m) T U hUo
  have hWU : ∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g := fun u hu g => by
    rw [GlobalTheory.JSW.whit_mul_right]
    exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hU u hu z)
  have hWK : ∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g :=
    fun k hk h1 h2 g => by
      rw [GlobalTheory.JSW.whit_mul_right]
      exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hK k hk h1 h2 z)
  let αc : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ := fun w i => ((α w i : ℂˣ) : ℂ)
  have hpw := GlobalTheory.T.cell_identity_rankinSelberg_torus_translate E m T ϖ hϖ αc F l₀ U Φ J hl₀ hWU hWK hWN hprof hΦr hJ0
    (fun y hy => (horb y hy).imp fun κ hκ => ⟨hκ.1, hκ.2.2⟩)
  obtain ⟨K, hKc, hKp⟩ := GlobalTheory.T.cell_decomposition_lattice_integral_unfolding E m T ϖ hϖ F l₀ U Φ J C hC hl₀ hWU hWK hWN hCp hΦc hΦr hJ0 horb
  obtain ⟨hBc, hBN, hBtop⟩ := GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant E (m + 1) (Fin.last m) (by simp) F Φ J (Pi.single (Fin.last m) 1) hWc hWN
    hΦs.continuous hΦr
  have hΦ1' : Φ (Pi.single (Fin.last m) 1) ≠ 0 := fun h => by rw [h] at hΦ1; simp at hΦ1
  have hone := GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity E m T ϖ F Φ J l₀ hl₀ hW0 hΦ1'
  refine ⟨α, Fin.last m, Φ, J, Pi.single (Fin.last m) 1, π₀, ω, φ, by simp, hα, hmk, hωu, hω, Or.inr hF, ?_, hΦs,
    hΦc, hΦr, hΦreal, fun h => hΦ1' (congrFun h _), ?_⟩
  · intro h
    apply hW0
    have e : F = 0 := congrArg Subtype.val h
    rw [e]
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  intro μ _ 𝓕₀ h𝓕

  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → GA E (m + 1) → ℝ, B = fun x g =>
      (GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g)).toReal :=
    ⟨_, rfl⟩
  have hB1 : Continuous (Function.uncurry B) := by
    have h1 : Continuous fun p : ℝ × GA E (m + 1) => (p.1, GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have h2' := hBc.comp h1
    have h2 : Continuous fun p : ℝ × GA E (m + 1) => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) p.1
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) := h2'
    have h3 := ENNReal.continuousOn_toReal.comp_continuous h2 fun p => hBtop _ _
    subst hBdef
    exact h3
  have hBg : ∀ (x : ℝ) (h : GA E (m + 1) → GA E (m + 1)), Continuous h →
      Continuous fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (h g) := by
    intro x h hh
    have h2 := hBc.comp (continuous_const.prodMk hh : Continuous fun g => (x, h g))
    exact h2
  have hB2 : ∀ x g, 0 ≤ B x g := fun _ _ => by rw [hBdef]; exact ENNReal.toReal_nonneg
  have hB3 : ∀ x, 0 < B x 1 := fun x => by
    rw [hBdef]
    refine ENNReal.toReal_pos ?_ (hBtop _ _)
    rw [mul_one]
    exact hone x
  have hB4 : ∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B x (u * g) = B x g := fun x u hu g => by
    rw [hBdef]
    beta_reduce
    have e : GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * (u * g) =
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * u * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1)⁻¹) * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) := by
      group
    rw [e, hBN x _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu)]
  have hB5 : ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ x g, g ∈ GlobalTheory.CellDec.C0 E (m + 1) T → B x g ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K :=
    ⟨K, hKc, fun x g hg h => hKp x g hg fun h0 => h (by rw [hBdef]; simp only; rw [h0]; rfl)⟩
  obtain ⟨hI, hIc⟩ := GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous E (m + 1) μ T 𝓕₀ h𝓕 B hB1 hB2 hB3 hB4 hB5
  have hd : 0 < GlobalTheory.CellDec.dinv (m + 1) l₀.1 := by
    unfold GlobalTheory.CellDec.dinv
    refine Finset.prod_pos fun w _ => zpow_pos ?_ _
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    unfold Formalism.UG.qV
    exact_mod_cast (zero_lt_one.trans this)

  have key : ∀ x : ℝ, ∫⁻ g in 𝓕₀, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g ∂μ =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) αc x *
        (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ) := by
    intro x
    have hmeas : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, Measurable fun g =>
        GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) := fun l =>
      (hBg x _ (continuous_const.mul continuous_id)).measurable
    have hnm : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T) μ :=
      h𝓕.nullMeasurableSet.inter (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) T).measurableSet.nullMeasurableSet
    have hmx : Measurable fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g :=
      (hBg x (fun g => g) continuous_id).measurable
    rw [GlobalTheory.CellDec.cell_lintegral μ T ϖ hϖ 𝓕₀ h𝓕 _ hmx
      (hBN x), ← GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct E (m + 1) T αc x l₀, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have e1 : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
          GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ENNReal.ofReal (B x g) * GlobalTheory.RSCell.cellProd T αc x (l.1 - l₀.1) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hnm] with g hg
      rw [hpw x g hg.2 l, hBdef, ENNReal.ofReal_toReal (hBtop _ _)]
    have hm2 : Measurable fun g => ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * ENNReal.ofReal (B x g) := by
      rw [hBdef]
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hmeas l₀)))
    rw [e1, lintegral_mul_const _ hm2, mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
    ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal, ?_, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · have e : (fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal) =
        fun x => GlobalTheory.CellDec.dinv (m + 1) l₀.1 * (∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal := by
      funext x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
    rw [e]
    exact (continuous_const.mul hIc).continuousWithinAt
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI 1).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI 1).2.ne)
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI x).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne)
  · rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne), mul_comm]
    exact key x

end GlobalTheory.RSCell
