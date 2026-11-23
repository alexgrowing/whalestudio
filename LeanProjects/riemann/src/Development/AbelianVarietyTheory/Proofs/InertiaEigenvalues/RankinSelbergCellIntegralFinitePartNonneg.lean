import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfolding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaAboveDetOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaBelowDetOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.RSnmFT

open GlobalTheory.CellDec GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem blockGL_finGL {j n : ℕ} (hj : j ≤ n) (k : GL (Fin j) (Af E)) :
    blockGL hj (finGL E j k) = finGL E n (blockGL hj k) := by
  have hm : ∀ {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin j) R),
      Matrix.GeneralLinearGroup.map p (blockGL hj g) = blockGL hj (Matrix.GeneralLinearGroup.map p g) :=
    by
    intro R S _ _ p g
    ext a b
    simp [blockMat_apply]
    split_ifs <;> simp
  refine ga_ext ?_ ?_
  · rw [hm, pInf_finGL, pInf_finGL, map_one]
  · rw [hm, pFin_finGL, pFin_finGL]

omit [IsTotallyComplex E] in

theorem blockGL_mem_integral {j n : ℕ} (hj : j ≤ n) {k : GL (Fin j) (Af E)}
    (hk : k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E j) :
    blockGL hj k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff] at hk ⊢
  have hI : ∀ (g : GL (Fin j) (Af E)), (∀ a b, (g : Matrix (Fin j) (Fin j) (Af E)) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) →
      ∀ a b, ((blockGL hj g : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    intro g hg a b
    rw [coe_blockGL, blockMat_apply]
    split_ifs
    · exact hg _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hI k hk.1, ?_⟩
  rw [← map_inv]
  exact hI k⁻¹ hk.2

end GlobalTheory.RSnmFT

namespace GlobalTheory.RSnmFT

open GlobalTheory.CellDec GroundTheory.Automorphic.FourierWhittaker
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in
theorem map_blockGL {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {j n : ℕ} (hj : j ≤ n)
    (g : GL (Fin j) R) :
    Matrix.GeneralLinearGroup.map p (blockGL hj g) = blockGL hj (Matrix.GeneralLinearGroup.map p g) := by
  ext a b
  simp [blockMat_apply]
  split_ifs <;> simp

omit [IsTotallyComplex E] in

theorem blockGL_level {j n : ℕ} (hj : j ≤ n) (S : Finset (HeightOneSpectrum (𝓞 E))) {k : GL (Fin j) (Af E)}
    (hk1 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v j)
    (hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) :
    (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (blockGL hj k) ∈ KGL v n) ∧
      ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) (blockGL hj k) = 1 := by
  refine ⟨GlobalTheory.RSLocalPart.mem_integralFiniteGL_iff_KGL.1
    (blockGL_mem_integral hj (GlobalTheory.RSLocalPart.mem_integralFiniteGL_iff_KGL.2 hk1)), fun v hv => ?_⟩
  rw [map_blockGL, hkS v hv, map_one]

theorem uIntNM_decomp {m r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {φ : GA E (m + r + 1 + 1) → ℂ} {φ' : GA E (m + 1) → ℂ} {κ : GA E (m + 1) → ℝ} {F : (Fin (m + 1) → Ad E) → ℂ}
    (hN : ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g)
    (hN' : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g)
    (hK : ∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g)
    (hK' : ∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g)
    (hM : ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h)
    (hF : ∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0)
    {u h g : GA E (m + 1)} {k : GL (Fin (m + 1)) (Af E)} (hu : u ∈ GlobalTheory.CellDec.NA E (m + 1)) (hh : h ∈ GlobalTheory.JSW.supS E (m + 1) S)
    (hk1 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1))
    (hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) (hg : g = u * h * finGL E (m + 1) k) :
    GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g) = GlobalTheory.JSW.psiN u * ((κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      GlobalTheory.JSW.whit φ' g = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' h ∧
      GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g =
        ((κ h * Complex.normSq (GlobalTheory.JSW.whit φ' h) * (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)).re *
          GlobalTheory.RSnm.detAbs g ^ (-((r : ℝ) + 1) / 2) : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := ⟨h1, h2⟩
  have hlev := blockGL_level (by omega : m + 1 ≤ m + r + 1 + 1) S hk1 hkS
  have hW : GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g) =
      GlobalTheory.JSW.psiN u * ((κ h : ℂ) * GlobalTheory.JSW.whit φ' h) := by
    rw [hg, map_mul, blockGL_finGL, hK _ hlev.1 hlev.2, map_mul,
      hN _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA _ hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL, hM h hh]
  have hW' : GlobalTheory.JSW.whit φ' g = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' h := by
    rw [hg, hK' k hk1 hkS, hN' u hu']
  refine ⟨hW, hW', ?_⟩
  have hp : GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.RSnmUnfProps.norm_psiN]; simp
  have hd : ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2) =
      ((GlobalTheory.RSnm.detAbs g ^ (-((r : ℝ) + 1) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (GlobalTheory.RSnm.detAbs_pos g).le]
    congr 1
    push_cast; ring
  set y := GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)
  have hy : y = (y.re : ℂ) := Complex.ext rfl (by simp [(hF _).2, y])
  have hw : GlobalTheory.JSW.whit φ' h * conj (GlobalTheory.JSW.whit φ' h) = (Complex.normSq (GlobalTheory.JSW.whit φ' h) : ℂ) := Complex.mul_conj _
  unfold GlobalTheory.RSnmUnf.uIntNM
  rw [hW, hW', hd, map_mul]
  change _ * _ * y * _ = _
  rw [hy]
  push_cast
  linear_combination ((κ h : ℂ) * (y.re : ℂ) * ((GlobalTheory.RSnm.detAbs g ^ (-((r : ℝ) + 1) / 2) : ℝ) : ℂ)) *
    (GlobalTheory.JSW.whit φ' h * conj (GlobalTheory.JSW.whit φ' h) * hp + hw)

end GlobalTheory.RSnmFT

namespace GlobalTheory.RSnmFT

open GroundTheory.Automorphic.FourierWhittaker
open scoped Pointwise

theorem integrableOn_cell_pos {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) {𝓕 : Set (GA E n)} (h𝓕 : IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ)
    {B : GA E n → ℝ} (hc : Continuous B) (hB0 : ∀ g, 0 ≤ B g)
    (hN : ∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, B (u * g) = B g) {K : Set (GA E n)} (hK : IsCompact K)
    (hs : ∀ g ∈ GlobalTheory.CellDec.C0 E n S, B g ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E n, u * g ∈ K)
    (h1 : ∃ g ∈ GlobalTheory.CellDec.C0 E n S, B g ≠ 0) :
    IntegrableOn B (𝓕 ∩ GlobalTheory.CellDec.C0 E n S) μ ∧ 0 < ∫ g in 𝓕 ∩ GlobalTheory.CellDec.C0 E n S, B g ∂μ := by
  obtain ⟨D, hD, hDu⟩ := GlobalTheory.RSLocalPart.exists_isCompact_unip E n
  haveI := GlobalTheory.ThetaUnfold.countable_range_ratGL (E := E) (a := n)
  haveI : Countable (GlobalTheory.CellDec.NE E n) :=
    (Subgroup.inclusion_injective (Subgroup.map_le_range (ratGL E n) _)).countable
  obtain ⟨i1, -, i3⟩ := GlobalTheory.RSLocalPart.integral_family_pos μ (GlobalTheory.CellDec.NE E n) h𝓕 (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E n S)
    (hD.mul hK) (fun γ hγ g hg => GlobalTheory.CellDec.adelicUnitriangular_mul_mem_unipotentTimesIntegral (GlobalTheory.RSLocalPart.NE_le hγ) hg) (B := fun _ => B)
    (hc.comp continuous_snd) (fun _ => hB0) (fun _ γ hγ => hN γ (GlobalTheory.RSLocalPart.NE_le hγ))
    (fun _ g hg h0 => by
      obtain ⟨u, hu, hk⟩ := hs g hg h0
      obtain ⟨γ, hγ, hd⟩ := hDu _ (inv_mem hu)
      exact ⟨γ, hγ, _, hd, _, hk, by group⟩)
    fun _ => h1
  exact ⟨i1 0, i3 0⟩

theorem exists_f_t_core : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
    Continuous κ → (∀ h, 0 ≤ κ h) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
    (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 ∧ 0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h₀)).re) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) → (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
        (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g = (f g : ℂ)) ∧
        (∀ (x : ℝ) (g : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) = Complex.exp (x * t g)) ∧
        (∀ x : ℝ, ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∂μ ≠ ⊤) := by
  intro E _ _ _ m r S φ φ' κ F hWc hWc' hN hN' hK hK' hM _ hκ0 ⟨C, hC, hκC⟩ ⟨h₀, hh₀, hκ₀, hW₀, hF₀⟩ hFc hFr μ _ 𝓕₀ h𝓕
  obtain ⟨hWb, hFl, -, hinv, -⟩ := GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hN hN' hFc
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have hO := GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S
  have hdc : ∀ s : ℝ, Continuous fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ s := fun s =>
    GlobalTheory.RSnm.continuous_detAbs.rpow_const fun g => Or.inl (GlobalTheory.RSnm.detAbs_pos g).ne'
  have hdp : ∀ (s : ℝ) (g : GA E (m + 1)), 0 < GlobalTheory.RSnm.detAbs g ^ s := fun s g =>
    Real.rpow_pos_of_pos (GlobalTheory.RSnm.detAbs_pos g) s
  set U : GA E (m + 1) → ℂ := GlobalTheory.RSnmUnf.uIntNM hmn F φ φ' 0 with hU
  have hUc : Continuous U :=
    ((hWb.mul (Complex.continuous_conj.comp hWc')).mul hFl).mul
      ((Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
        fun g => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos g))
  have hUW : ∀ g, U g ≠ 0 → GlobalTheory.JSW.whit φ (blockGL hmn g) ≠ 0 := fun g h0 h => h0 (by
    simp only [hU, GlobalTheory.RSnmUnf.uIntNM, h, zero_mul])

  set K : Set (GA E (m + 1)) :=
    C * (finGL E (m + 1) '' (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set _)) with hKdef
  have hKc : IsCompact K := hC.mul ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1)).image
    GlobalTheory.RSLocalPart.continuous_finGL)
  have hKs : ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.JSW.whit φ (blockGL hmn g) ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
    intro g hg h0
    obtain ⟨u, hu, h, hh, k, hk1, hkS, e⟩ := GlobalTheory.CellDec.exists_mul_supS_finGL E (m + 1) S g hg
    have hκ : κ h ≠ 0 := fun hz => h0 (by
      rw [(uIntNM_decomp hN hN' hK hK' hM hFr hu hh hk1 hkS e).1, hz]; simp)
    obtain ⟨u', hu', hc'⟩ := hκC h hh hκ
    have hu'N : u' ∈ GlobalTheory.CellDec.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB _).2 hu'
    refine ⟨(u * u')⁻¹, inv_mem (mul_mem hu hu'N), _, hc', _,
      ⟨k, GlobalTheory.RSLocalPart.mem_integralFiniteGL_iff_KGL.2 hk1, rfl⟩, ?_⟩
    rw [e]
    group

  have hUr : ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, U g = (‖U g‖ : ℂ) := by
    intro g hg
    obtain ⟨u, hu, h, hh, k, hk1, hkS, e⟩ := GlobalTheory.CellDec.exists_mul_supS_finGL E (m + 1) S g hg
    rw [hU, (uIntNM_decomp hN hN' hK hK' hM hFr hu hh hk1 hkS e).2.2, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (hκ0 h) (Complex.normSq_nonneg _)) (hFr _).1) (hdp _ g).le)]

  have h₀C : h₀ ∈ GlobalTheory.CellDec.C0 E (m + 1) S := by
    refine ⟨1, one_mem _, h₀, ?_, (one_mul _).symm⟩
    simp only [GlobalTheory.CellDec.US, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v hv
    rw [show GlobalTheory.CellDec.compV E (m + 1) v h₀ = 1 from hh₀ v hv]
    exact one_mem _
  have hU₀ : U h₀ ≠ 0 := by
    rw [hU, (uIntNM_decomp hN hN' hK hK' hM hFr (k := 1) (g := h₀) (one_mem _) hh₀ (fun v => by rw [map_one]; exact one_mem _)
      (fun v _ => map_one _) (by rw [map_one, one_mul, mul_one])).2.2]
    exact Complex.ofReal_ne_zero.2
      (mul_pos (mul_pos (mul_pos hκ₀ (Complex.normSq_pos.2 hW₀)) hF₀) (hdp _ _)).ne'
  obtain ⟨hIB, hpos⟩ := integrableOn_cell_pos μ S h𝓕 hUc.norm (fun g => norm_nonneg _)
    (fun u hu g => by rw [hU, (hinv u hu g).2.2.2.2 0]) hKc
    (fun g hg h0 => hKs g hg (hUW g (norm_ne_zero_iff.1 h0))) ⟨h₀, h₀C, norm_ne_zero_iff.2 hU₀⟩
  have htc : Continuous fun g : GA E (m + 1) => Real.log (GlobalTheory.RSnm.detAbs g) :=
    GlobalTheory.RSnm.continuous_detAbs.log fun g => (GlobalTheory.RSnm.detAbs_pos g).ne'
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
  refine ⟨(GlobalTheory.CellDec.C0 E (m + 1) S).indicator fun g => ‖U g‖, fun g => Real.log (GlobalTheory.RSnm.detAbs g),
    hUc.norm.measurable.indicator hO.measurableSet, htc.measurable,
    fun g => Set.indicator_nonneg (fun g _ => norm_nonneg _) g, ?_, ?_, ⟨R, fun g hg => ?_⟩,
    fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_, fun x => ?_⟩
  · unfold IntegrableOn
    rw [integrable_indicator_iff hO.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
    exact hIB
  · rwa [integral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
  · have hgC : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hgC] at hg
    obtain ⟨u, hu, hk⟩ := hKs g hgC (hUW g (norm_ne_zero_iff.1 hg))
    have := hR _ hk
    rwa [(hinv u hu g).2.2.2.1, Real.norm_eq_abs] at this
  · rw [Set.indicator_of_mem hg]
    exact hUr g hg
  · rw [Real.rpow_def_of_pos (GlobalTheory.RSnm.detAbs_pos g), Complex.ofReal_exp]
    push_cast
    rw [mul_comm]
  · have hF0 : GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h₀) ≠ 0 := fun h => by
      rw [h] at hF₀; simp at hF₀
    obtain ⟨hI, -⟩ := integrableOn_cell_pos μ S h𝓕
      (B := fun g => ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)))
      (((hWb.norm.pow 2).mul hFl.norm).mul (hdc _))
      (fun g => mul_nonneg (by positivity) (hdp _ g).le)
      (fun u hu g => by
        obtain ⟨h1, -, h3, h4, -⟩ := hinv u hu g
        simp only [h1, h3, h4]) hKc
      (fun g hg h0 => hKs g hg fun h => h0 (by simp [h]))
      ⟨h₀, h₀C, (mul_pos (mul_pos (pow_pos (norm_pos_iff.2 (hUW _ hU₀)) 2) (norm_pos_iff.2 hF0)) (hdp _ _)).ne'⟩
    refine ne_of_eq_of_ne (lintegral_congr fun g => ?_) (Integrable.lintegral_lt_top hI).ne
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]

end GlobalTheory.RSnmFT

namespace GlobalTheory.RSnmFT

open GlobalTheory.RSUnfoldW GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped NNReal

theorem lintegral_whit_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G : (Fin (m + 1) → Ad E) → ℂ, Continuous G →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ 𝓕 : Set (GA E (m + 1)), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ ∧ ∀ x : ℝ,
      ∫⁻ g in 𝓕₀, ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 * ‖G (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ =
      ∫⁻ g in 𝓕, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ := by
  intro E _ _ _ m π hπ F hF G hG μ _ 𝓕₀ h𝓕₀
  obtain ⟨φ, hφ, hφF⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπ hF
  have hB : IsBCC F := by
    have h := (GlobalTheory.JSW.mem_dSub.1 hφ []).2
    rw [GlobalTheory.JSW.word_nil] at h
    rw [← hφF]
    exact h
  haveI : DiscreteTopology (ratMirU E (m + 1) m) := GlobalTheory.MirTower.discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI : DiscreteTopology (ratGL E (m + 1)).range := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  obtain ⟨𝓕P, h𝓕P⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratMirU E (m + 1) m) μ
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratGL E (m + 1)).range μ
  refine ⟨𝓕, h𝓕, fun x => ?_⟩
  have hℓ : ((Fin.last m : Fin (m + 1)) : ℕ) + 1 = m + 1 := rfl
  have hdet : ∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.RSnm.detAbs (ratGL E (m + 1) γ * g) = GlobalTheory.RSnm.detAbs g := by
    intro γ g
    unfold GlobalTheory.RSnm.detAbs
    rw [map_mul, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hmd : Measurable fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ x := GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const x
  have hmeas : ∀ v : Fin (m + 1) → E, Measurable fun g : GA E (m + 1) =>
      ‖F g‖ₑ ^ 2 * ‖G (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)‖ₑ *
        ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) := by
    intro v
    have hv : Continuous fun g : GA E (m + 1) => Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val :=
      continuous_const.matrix_vecMul Units.continuous_val
    exact ((hB.cont.enorm.measurable.pow_const 2).mul (hG.comp hv).enorm.measurable).mul
      (ENNReal.measurable_ofReal.comp hmd)
  have e1 := GlobalTheory.T.lintegral_theta_series_unfold_mirabolic E (m + 1) (Nat.succ_pos m) μ 𝓕 𝓕P h𝓕 h𝓕P
    (fun g y => ‖F g‖ₑ ^ 2 * ‖G y‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x))
    hmeas (fun γ g y => by simp only [hB.left, hdet])
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [e1]
  set ψC : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E) with hψC
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := by rw [ratMirU_zero]; exact h𝓕₀
  set w : GA E (m + 1) → ℝ≥0 := fun g => ‖G (g.val (Fin.last m))‖₊ * Real.toNNReal (GlobalTheory.RSnm.detAbs g ^ x) with hw
  have hrow : Continuous fun g : GA E (m + 1) => g.val (Fin.last m) :=
    continuous_pi fun i => Units.continuous_val.matrix_elem (Fin.last m) i
  have hwm : Measurable w := (hG.comp hrow).nnnorm.measurable.mul (measurable_real_toNNReal.comp hmd)
  have hwl : ∀ γ ∈ mirU E (m + 1) (m + 1 - 1), ∀ g, w (ratGL E (m + 1) γ * g) = w g := by
    intro γ hγ g
    simp only [hw]
    rw [row_mul (ratGL_row hℓ hγ), hdet]
  have hwu : ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), w (blkU y * g) = w g := by
    intro k y g
    simp only [hw, GlobalTheory.RSnm.detAbs]
    rw [row_mul (blkU_row hℓ y), map_mul, det_blkU, one_mul]
  have hgood : Good ψC (m + 1 - 1) F := GlobalTheory.CuspGeneric.good_top E m ψC F hB.cont hB.left
    fun r hr hra g => GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero E (m + 1) F hB.cont hB.left hB.cusp r hr hra g
  have e2 := (GlobalTheory.T.unfold_mirabolic_alt E (m + 1) μ ψC (GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar E) 𝓕P 𝓕₀ h𝓕P h𝓕₀' w hwm hwl hwu).1 F hgood
  rw [GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker E (m + 1) F (Nat.succ_pos m) hB.cont hB.left] at e2
  simp_rw [mul_assoc]
  exact e2.symm

end GlobalTheory.RSnmFT

namespace GlobalTheory.RSnmFT

theorem lintegral_whit_sq_ne_top {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}
    {π' : CuspSub E (m + 1)} (hπ : π'.IsUnitary) {φ' : GA E (m + 1) → ℂ} (hφ : φ' ∈ GlobalTheory.JSW.mspanR π')
    {G : (Fin (m + 1) → Ad E) → ℂ} (hG : G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)))
    (hGc : Continuous G) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] {𝓕₀ : Set (GA E (m + 1))}
    (h𝓕 : IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ) {x : ℝ} (hx : 1 < x) :
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 * ‖G (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  obtain ⟨𝓕, h1, h2⟩ := lintegral_whit_sq_eq E m π' hπ φ' hφ G hGc μ 𝓕₀ h𝓕
  have hup := GlobalTheory.T.lintegral_theta_above_det_one E m π' hπ φ' hφ G hG μ 𝓕 h1 x
  have hlow := GlobalTheory.T.lintegral_theta_below_det_one E m π' hπ φ' hφ G hG μ 𝓕 h1 x hx
  have hsub : 𝓕 ⊆ (𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}) ∪ (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) := fun g hg =>
    (le_total 1 (GlobalTheory.RSnm.detAbs g)).imp (fun h => ⟨hg, h⟩) fun h => ⟨hg, h⟩
  rw [h2 x]
  exact ne_of_lt ((lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt
    (ENNReal.add_lt_top.2 ⟨hup.lt_top, hlow.lt_top⟩)))

theorem exists_cellPart_unfoldedIntegral_positive_alt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
    Continuous κ → (∀ h, 0 ≤ κ h) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
    (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 ∧ 0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h₀)).re) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) → (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
        (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g = (f g : ℂ)) ∧
        (∀ (x : ℝ) (g : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) = Complex.exp (x * t g)) ∧
        (∀ x : ℝ, ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∂μ ≠ ⊤) ∧
        (∀ π' : CuspSub E (m + 1), π'.IsUnitary → φ' ∈ GlobalTheory.JSW.mspanR π' →
          F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)) → ∀ x : ℝ, 1 < x →
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ' (g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ x)) ∂μ ≠ ⊤) := by
  intro E _ _ _ m r S φ φ' κ F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hFc h13 μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    exists_f_t_core E m r S φ φ' κ F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hFc h13 μ 𝓕₀ h𝓕
  refine ⟨f, t, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun π' hπ hφ hF x hx => ?_⟩
  exact ne_top_of_le_ne_top (lintegral_whit_sq_ne_top hπ hφ
    (GroundTheory.Automorphic.GJMatrix.adelicFourierPi_mem_schwartzBruhatPi hF) hFc μ h𝓕 hx)
    (lintegral_mono_set Set.inter_subset_left)

end GlobalTheory.RSnmFT
