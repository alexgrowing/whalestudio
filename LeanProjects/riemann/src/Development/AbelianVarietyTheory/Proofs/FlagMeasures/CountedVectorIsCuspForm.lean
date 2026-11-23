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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRowsStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCusp

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨hR1, hRmul, hRnorm, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B

  have hπ1 : (fun a : B.I.Gf => B.R (1, a)) 1 = 1 := hR1
  have hπmul : ∀ a b : B.I.Gf, (fun a : B.I.Gf => B.R (1, a)) (a * b) =
      (fun a : B.I.Gf => B.R (1, a)) a * (fun a : B.I.Gf => B.R (1, a)) b := by
    intro a b
    have hab : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by
      simp [Prod.mk_mul_mk]
    simp only
    rw [hab, hRmul]
  have hadj : ∀ (a : B.I.Gf) (u v : B.I.L2 B.μf B.fund),
      ⟪u, B.R (1, a) v⟫_ℂ = ⟪B.R (1, a⁻¹) u, v⟫_ℂ :=
    GlobalTheory.IdemProj.inner_rep (fun a : B.I.Gf => B.R (1, a)) hπ1 hπmul (fun a v => hRnorm _ v)

  have hone : (1 : B.I.Gf) ∈ B.I.Kg B.g := by
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · show ((1 : B.I.Gf) : GL (Fin B.I.n) (TensorProduct B.I.F B.I.E (Af B.I.F))) ∈ Formalism.UG.stabGL B.I.Lf
      simpa using (Formalism.UG.stabGL B.I.Lf).one_mem
    · simp [AutInst.fmat]
  have he : ∀ x, B.e (k * x) = B.e x := by
    intro x
    have h' := B.e_adm.2.2.2.2.2.1 x k hk 1 hone
    rwa [mul_one] at h'
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.comp_apply, hadj, B.Re_spec.2, B.Re_spec.2]
  have hshift : ∀ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ =
      (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) := by
    intro g
    simp only
    rw [he, ← inv_inv k, ← hadj, inv_inv, ← ContinuousLinearMap.mul_apply, ← hπmul]
  calc ∫ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ ∂B.μf
      = ∫ g, (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) ∂B.μf := by
        congr 1
        funext g
        exact hshift g
    _ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf :=
        integral_mul_left_eq_self (μ := B.μf) (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hcont, hbound, hmaj⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl

  have hgap : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hqR : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hq
      have hnR : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.mpr hqR
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
          (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hqR, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hv := hh v
      rw [hpow] at hv
      have hpos : 0 < (B.I.n : ℝ) * (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        positivity
      nlinarith
  have hint : Integrable (majPh B d h) (muInf B.I) := by
    simpa using hmaj 0 le_rfl hgap
  exact hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem row_isCuspFn : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro hSL B d h hd hg hh hl hH T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  ·
    intro W hW
    exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.2 (by omega)
  have hn : 1 ≤ B.I.n := hnpos

  obtain ⟨A₀, hA₀, hAeq⟩ := Submodule.mem_map.mp hA
  have hAc : A = B.Re.comp A₀ := hAeq.symm
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hcomm : ∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re :=
    (GlobalTheory.IdemProj.re_orth_proj B).2.1
  have hAS : A ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, A.comp (B.σs g) = (B.R (g, 1)).comp A
    intro g
    rw [hAc, ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]

  have hfix : ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w) := by
    intro k hk
    rw [hAc]
    exact congrArg (fun L : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => L (A₀ (B.tens B.w)))
      (level_comp_Re B k hk hg)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows hSL B d hd hn hg
  obtain ⟨f, hf, hfb⟩ := hC A hAS hfix

  have hTy : T (A (B.tens B.w)) = A (B.tens B.w) :=
    ((GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hn hh hl)).2.2.2 T hT).2.1 A hA
  exact (GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth B d h hd (GlobalTheory.T.integral_discreteSeries_unipotent_vanishes hSL B d h hd hl hh) hl hH T hT (A (B.tens B.w)) f
    (C * ‖A (B.tens B.w)‖) hTy hf (fun x => (hfb x).trans_eq (by ring))).2

end GlobalTheory.RowCusp
