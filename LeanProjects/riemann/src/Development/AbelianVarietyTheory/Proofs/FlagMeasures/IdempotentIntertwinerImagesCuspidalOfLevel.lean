import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKTypeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAllKType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  simp only [AutInst.Kg, AutInst.Kset, Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · simp
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hbi, -⟩ := B.e_adm

  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun a => B.R (1, a) with hπ
  have hπ1 : π 1 = 1 := h1
  have hπm : ∀ a b, π (a * b) = π a * π b := fun a b => by
    simp only [hπ]
    rw [← hm]
    congr 1
    ext <;> simp
  have hπn : ∀ a v, ‖π a v‖ = ‖v‖ := fun a v => hn _ v

  have hek : ∀ x, B.e (k * x) = B.e x := fun x => by
    simpa using hbi x k hk 1 (one_mem_Kg B.I B.g)
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change ⟪x, π k (B.Re y)⟫_ℂ = _
  rw [GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (B.Re y), B.Re_spec.2 (π k⁻¹ x) y, B.Re_spec.2 x y]
  have hinner : ∀ a, ⟪π k⁻¹ x, B.R (1, a) y⟫_ℂ = ⟪x, B.R (1, k * a) y⟫_ℂ := fun a => by
    have := (GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (π a y)).symm
    change ⟪π k⁻¹ x, π a y⟫_ℂ = ⟪x, π (k * a) y⟫_ℂ
    rw [this, hπm, ContinuousLinearMap.mul_apply]
  simp_rw [hinner]
  calc ∫ a, B.e a * ⟪x, B.R (1, k * a) y⟫_ℂ ∂B.μf
      = ∫ a, (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) (k * a) ∂B.μf := by
        congr 1
        ext a
        simp only [hek]
    _ = ∫ a, B.e a * ⟪x, B.R (1, a) y⟫_ℂ ∂B.μf := by
        exact integral_mul_left_eq_self (μ := B.μf) (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hmaj := hint 0 le_rfl (fun v => by
    by_cases hq : rkR (B.I.ε v) = 0
    · exact Or.inl hq
    right

    have hqn : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
    have hqn' : (rkR (B.I.ε v) : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hqn
    have hs : 0 < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hn : 0 < (B.I.n : ℝ) := by linarith
    have hns : 0 < (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := mul_pos hn hs
    have h1 : (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (rkR (B.I.ε v) : ℝ)
        ≤ (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) :=
      mul_le_mul_of_nonneg_left hqn' hns.le
    have h2 := hb v
    nlinarith)
  simp only [zero_mul, Real.exp_zero, mul_one] at hmaj
  exact hmaj.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)

theorem cusp_all : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro B d h hd hK hg hh hl hb A hA

  obtain ⟨T0, hT0, hA'⟩ := Submodule.mem_map.1 hA
  have hAe : A = B.Re.comp T0 := by rw [← hA']; rfl
  subst hAe
  have hT0' : ∀ g : B.I.Ginf, T0.comp (B.σs g) = (B.R (g, 1)).comp T0 := hT0
  have hint := integrable_ph B d h hd hl hb
  obtain ⟨-, hcomm, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hHom : ∀ g : B.I.Ginf, (B.Re.comp T0).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp T0) := fun g => by
    rw [ContinuousLinearMap.comp_assoc, hT0' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  refine ⟨hHom, fun u => ?_⟩

  obtain ⟨S, hSmem, hScl, hSinv, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, hirr, -, hnorm, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hw := GlobalTheory.T.countedVectors_are_cuspForms_singleLowestKType B d h hd hK hg hh hl hb T hT (B.Re.comp T0) hA
  let S' : Submodule ℂ B.Hs := S.comap ((B.Re.comp T0 : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)
  have hS'cl : IsClosed (S' : Set B.Hs) := hScl.preimage (B.Re.comp T0).continuous
  have hS'inv : ∀ g, ∀ v ∈ S', B.σs g v ∈ S' := fun g v hv => by
    have hv' : (B.Re.comp T0) v ∈ S := hv
    show (B.Re.comp T0) (B.σs g v) ∈ S
    have := congrArg (fun F : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => F v) (hHom g)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
    exact hSinv _ _ hv'
  have hwS : B.tens B.w ∈ S' := (hSmem _).2 hw
  rcases hirr S' hS'cl hS'inv with h0 | htop
  · exfalso
    rw [h0, Submodule.mem_bot] at hwS
    rw [hwS, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · have hu : u ∈ S' := htop ▸ Submodule.mem_top
    refine ⟨(hSmem _).1 hu, fun k hk => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re, re_fixed B k hk]

end GlobalTheory.Dec.CuspAllKType
