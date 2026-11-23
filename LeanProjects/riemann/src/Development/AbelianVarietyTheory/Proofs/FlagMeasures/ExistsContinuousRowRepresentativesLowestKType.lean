import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebrStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothRepsType

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

theorem exists_level_bump (B : RowsAut) (hg : 1 ≤ B.g) :
    ∃ χ : B.I.Gf → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) ∧
      ∫ k, χ k ∂B.μf = 1 := by
  obtain ⟨hT, -, -, hKc, -, -, hK⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨ho, ⟨K, hKe⟩, -⟩ := hK B.g hg
  have hcl : IsClosed (B.I.Kg B.g) := by
    rw [← hKe] at ho ⊢
    exact K.isClosed_of_isOpen ho
  have hc : IsCompact (B.I.Kg B.g) := hKc.of_isClosed_subset hcl fun x hx => hx.1
  have hne : (B.I.Kg B.g).Nonempty := by
    rw [← hKe]; exact ⟨1, K.one_mem⟩
  have hpos : 0 < B.μf.real (B.I.Kg B.g) :=
    ENNReal.toReal_pos (ho.measure_pos B.μf hne).ne' hc.measure_lt_top.ne
  refine ⟨(B.I.Kg B.g).indicator fun _ => (((B.μf.real (B.I.Kg B.g))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
  · intro k hk
    exact Set.mem_of_indicator_ne_zero hk
  · rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

theorem integrable_of_prod (B : RowsAut) (hσ : IsURep B.σs) (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ)
    (h1 : ∫ k, χ k ∂B.μf = 1) (hc : Continuous fun y : B.I.GA => a y.1 * χ y.2)
    (hs : HasCompactSupport fun y : B.I.GA => a y.1 * χ y.2) (w : B.Hs) :
    Integrable (fun g => a g • B.σs g w) (muInf B.I) := by
  obtain ⟨k, hk⟩ : ∃ k, χ k ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at h1
  have hac : Continuous a := by
    have h2 : Continuous fun g : B.I.Ginf => a g * χ k :=
      hc.comp (f := fun g : B.I.Ginf => ((g, k) : B.I.GA)) (Continuous.prodMk_left k)
    have h3 := h2.mul_const (χ k)⁻¹
    simpa [mul_assoc, mul_inv_cancel₀ hk] using h3
  have has : HasCompactSupport a := by
    refine HasCompactSupport.intro (hs.isCompact.image continuous_fst) fun g hg => ?_
    by_contra h0
    exact hg ⟨(g, k), subset_tsupport _ (mul_ne_zero h0 hk), rfl⟩
  have : IsFiniteMeasureOnCompacts (muInf B.I) := by unfold muInf; infer_instance
  exact (hac.smul (hσ.2.2.2 w)).integrable_of_hasCompactSupport has.smul_right

theorem conv_avg (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : T ∈ B.I.HomS B.σs B.μf B.fund B.R) (hk : ∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u)
    (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ) (hχ : ∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) (h1 : ∫ k, χ k ∂B.μf = 1)
    (w : B.Hs) (hint : Integrable (fun g => a g • B.σs g w) (muInf B.I)) :
    ∫ y, (a y.1 * χ y.2) • B.R y (T w) ∂(B.I.muA B.μf) = T (∫ g, a g • B.σs g w ∂(muInf B.I)) := by
  have : SigmaFinite (muInf B.I) := by unfold muInf; infer_instance
  obtain ⟨-, hmul, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have hpt : ∀ y : B.I.GA, (a y.1 * χ y.2) • B.R y (T w) = χ y.2 • T (a y.1 • B.σs y.1 w) := by
    rintro ⟨g, k⟩
    by_cases h0 : χ k = 0
    · simp [h0]
    · have e1 : B.R (g, k) (T w) = T (B.σs g w) := by
        have : ((g, k) : B.I.GA) = (g, 1) * (1, k) := by simp
        rw [this, hmul, ContinuousLinearMap.mul_apply, hk w k (hχ k h0)]
        exact (congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S w) (hT g)).symm
      simp only [e1, map_smul, smul_smul, mul_comm]
  simp_rw [hpt]
  change ∫ y : B.I.Ginf × B.I.Gf, χ y.2 • T (a y.1 • B.σs y.1 w) ∂((muInf B.I).prod B.μf) = _
  rw [← integral_prod_swap]
  have := integral_prod_smul (μ := B.μf) (ν := muInf B.I) χ (fun g => T (a g • B.σs g w))
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [this, h1, one_smul, T.integral_comp_comm hint]

theorem repsExist : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v))
      (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g →
    ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) →
      ∃ Fr, IsReps B T Fr := by
  intro B d hd h1 hg T hT hk
  classical
  obtain ⟨χ, hχc, hχs, hχK, hχ1⟩ := exists_level_bump B hg
  obtain ⟨huniq, -, htr, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hd).1
  let Fr : B.Hs → B.I.GA → ℂ := fun u => if h : ∃ f, IsContRep B (T u) f then h.choose else 0
  have hFr : ∀ u f, IsContRep B (T u) f → Fr u = f := by
    intro u f hf
    have h : ∃ f, IsContRep B (T u) f := ⟨f, hf⟩
    have : Fr u = h.choose := dif_pos h
    rw [this]
    exact huniq _ _ _ h.choose_spec hf
  refine ⟨Fr, fun P u hu => ?_⟩
  obtain ⟨A, hA, hAs, hfix⟩ := GlobalTheory.T.exists_smooth_average_lowest_KType B d hd h1 P u hu
  let ψ : B.I.GA → ℂ := fun y => A (fun v i j => uMat (y.1 v) i j) * χ y.2
  have hder := fun E => GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra B A χ ψ E hA hAs hχc hχs (fun _ => rfl)
  have hψ : ∫ y, ψ y • B.R y (T (B.tens B.w)) ∂(B.I.muA B.μf) = T u := by
    rw [hfix]
    exact conv_avg B T hT hk (fun g => A (fun v i j => uMat (g v) i j)) χ hχK hχ1 _
      (integrable_of_prod B hσ (fun g => A (fun v i j => uMat (g v) i j)) χ hχ1 (hder 0).1 (hder 0).2.1 _)
  have hrep := GlobalTheory.ConvContRep.conv_isContRep B ψ (T (B.tens B.w)) (hder 0).1 (hder 0).2.1
  rw [hψ] at hrep
  have hFu := hFr u _ hrep
  have hrep' : IsContRep B (T u) (Fr u) := by rw [hFu]; exact hrep
  refine ⟨hrep', fun k hkK y => ?_, fun E y => ?_⟩
  · have := htr _ _ (1, k) hrep'
    rw [hk u k hkK] at this
    exact congrFun (huniq _ _ _ this hrep') y
  · obtain ⟨-, -, ψ', hc', hs', hd'⟩ := hder E
    obtain ⟨hd1, hd2⟩ := hd' (T (B.tens B.w))
    rw [hψ] at hd1
    obtain ⟨A', -, -, hA'⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B A E (B.tens B.w) hσ hA hAs
    rw [← hfix] at hA'
    have hdiff : HasDerivAt (orbit B E u) (dAct B E u) 0 := hA'.differentiableAt.hasDerivAt
    have hd3 : HasDerivAt (fun t : ℝ => T (orbit B E u t)) (T (dAct B E u)) 0 :=
      (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hdiff
    have hfun : (fun t : ℝ => T (orbit B E u t)) =
        fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (T u) := by
      funext t
      exact congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S u) (hT _)
    rw [hfun] at hd3
    have heq := hd3.unique hd1
    have hrep2 := GlobalTheory.ConvContRep.conv_isContRep B ψ' (T (B.tens B.w)) hc' hs'
    rw [← heq] at hrep2
    rw [hFr _ _ hrep2, hFu]
    exact hd2 y

end GlobalTheory.SmoothRepsType
