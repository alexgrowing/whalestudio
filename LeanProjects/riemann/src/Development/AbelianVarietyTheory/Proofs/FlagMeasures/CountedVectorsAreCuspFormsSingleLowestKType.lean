import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanishStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluationStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCuspKType

private theorem one_mem_Kg_flag_measures (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show (1 : I.Gf) ∈ I.Kset
    simp only [AutInst.Kset, Set.mem_ofPred_eq, OneMemClass.coe_one]
    exact one_mem _
  · simp only [AutInst.fmat, OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_mulVec, smul_zero]

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨h1, hm, hn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun g => B.R (1, g) with hπ
  have p1 : π 1 = 1 := h1
  have pm : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    have : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by simp
    simp only [hπ, this, hm]
  have pn : ∀ g v, ‖π g v‖ = ‖v‖ := fun g v => hn _ v
  have he : ∀ g, B.e (k * g) = B.e g := by
    intro g
    have := B.e_adm.2.2.2.2.2.1 g k hk 1 (one_mem_Kg_flag_measures B.I B.g)
    simpa using this
  ext1 y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change inner ℂ x (π k (B.Re y)) = _
  rw [GlobalTheory.IdemProj.inner_rep π p1 pm pn, B.Re_spec.2, B.Re_spec.2]
  have key : ∀ g, B.e g * inner ℂ (π k⁻¹ x) (B.R (1, g) y)
      = (fun g' => B.e g' * inner ℂ x (B.R (1, g') y)) (k * g) := by
    intro g
    have e1 : inner ℂ (π k⁻¹ x) (B.R (1, g) y) = inner ℂ x (π k (π g y)) := by
      rw [GlobalTheory.IdemProj.inner_rep π p1 pm pn k x]
    have e2 : π k (π g y) = B.R (1, k * g) y := by
      show π k (π g y) = π (k * g) y
      rw [pm]; rfl
    simp only [e1, e2, he]
  simp_rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun g' => B.e g' * inner ℂ x (B.R (1, g') y)) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hb, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hcond : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | hpos
    · exact Or.inl h0
    · right
      have hq : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hpos
      have hnr : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
          = Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
          Real.rpow_add hq, Real.rpow_one]
      have hs : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr hq
      have hv := hh v
      rw [hpow] at hv
      have hpos' : 0 < Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) := by positivity
      nlinarith
  have hI := hi 0 le_rfl hcond
  simp only [zero_mul, Real.exp_zero, mul_one] at hI
  exact hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem row_isCuspFn : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro B d h hd hK hg hh hl hbig T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  · intro W hW
    have : IsEmpty (Fin B.I.n) := by rw [hn0]; infer_instance
    exact absurd (Submodule.eq_bot_of_subsingleton) hW.1
  have hn : 1 ≤ B.I.n := hnpos
  have hint := integrable_ph B d h hd hn hh hl
  obtain ⟨-, hcomm, -, hT'⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := (hT' T hT).2.1 A hA
  obtain ⟨A₀, hA₀, hAe⟩ := Submodule.mem_map.mp hA
  have hAe' : A = B.Re.comp A₀ := by rw [← hAe]; rfl
  subst hAe'
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hhom : B.Re.comp A₀ ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, (B.Re.comp A₀).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A₀)
    intro g
    rw [ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ B.I.Kg B.g, B.R (1, k) ((B.Re.comp A₀) (B.tens B.w)) = (B.Re.comp A₀) (B.tens B.w) := by
    intro k hk
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re,
      level_comp_Re B k hk hg]
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_continuousRepresentative_bounded_evaluation B d hd hK hn hg
  obtain ⟨f, hf, hfb⟩ := hC _ hhom hlev
  have hvan := GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish B d h hd hK hl hh
  refine (GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth B d h hd hvan hl hbig T hT _ f (C * ‖(B.Re.comp A₀) (B.tens B.w)‖) ?_ hf ?_).2
  · simpa using hfix
  · intro x
    exact (hfb x).trans_eq (by ring)

end GlobalTheory.RowCuspKType
