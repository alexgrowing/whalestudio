import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIrrAndDenseOfIsFdegG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjAbsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GlobProj

theorem weak_integral_prod {X Y H : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (R : X × Y → (H →L[ℂ] H)) (A : X → (H →L[ℂ] H)) (B : Y → (H →L[ℂ] H))
    (hR : ∀ g k, R (g, k) = A g * B k) (hn : ∀ z v, ‖R z v‖ = ‖v‖)
    (a : X → ℂ) (e : Y → ℂ) (ha : Integrable a μ) (he : Integrable e ν) (P E : H →L[ℂ] H)
    (hP : ∀ x y : H, ⟪x, P y⟫_ℂ = ∫ g, a g * ⟪x, A g y⟫_ℂ ∂μ)
    (hE : ∀ x y : H, ⟪x, E y⟫_ℂ = ∫ k, e k * ⟪x, B k y⟫_ℂ ∂ν) (x y : H)
    (hm : AEStronglyMeasurable (fun z => ⟪x, R z y⟫_ℂ) (μ.prod ν)) :
    ⟪x, (P.comp E) y⟫_ℂ = ∫ z, (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ ∂(μ.prod ν) := by
  have hbd : ∀ z, ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun z => by
    calc ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖R z y‖ := norm_inner_le_norm x _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hae : Integrable (fun z : X × Y => a z.1 * e z.2) (μ.prod ν) := ha.mul_prod he
  have hint : Integrable (fun z : X × Y => (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ) (μ.prod ν) := by
    refine Integrable.mono' (hae.norm.mul_const (‖x‖ * ‖y‖)) (hae.aestronglyMeasurable.mul hm) ?_
    refine ae_of_all _ fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd z) (norm_nonneg _)
  rw [integral_prod _ hint, ContinuousLinearMap.comp_apply, hP]
  congr 1
  funext g
  dsimp only
  have h1 : ⟪x, A g (E y)⟫_ℂ = ∫ k, e k * ⟪x, R (g, k) y⟫_ℂ ∂ν := by
    rw [← ContinuousLinearMap.adjoint_inner_left (A g) (E y) x, hE]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, hR, ContinuousLinearMap.mul_apply]
  rw [h1, ← integral_const_mul]
  congr 1
  funext k
  ring

theorem conv_prod (B : RowsAut) (a : B.I.Ginf → ℂ) (P : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (ha : Integrable a (muInf B.I)) (hP : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) a P) :
    B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) (P.comp B.Re) ∧
      ∀ T, B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) T → T = P.comp B.Re := by
  obtain ⟨-, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : SFinite (muInf B.I) := by unfold muInf; infer_instance
  have hE := B.Re_spec
  have key : ∀ x y : B.I.L2 B.μf B.fund, ⟪x, (P.comp B.Re) y⟫_ℂ =
      ∫ g, (fun z : B.I.GA => a z.1 * B.e z.2) g * ⟪x, B.R g y⟫_ℂ ∂(B.I.muA B.μf) := by
    intro x y
    have hm : AEStronglyMeasurable (fun z => ⟪x, B.R z y⟫_ℂ) ((muInf B.I).prod B.μf) :=
      (continuous_const.inner (hcont y)).aestronglyMeasurable
    exact weak_integral_prod (muInf B.I) B.μf B.R (fun g => B.R (g, 1)) (fun k => B.R (1, k))
      (fun g k => by rw [← hmul, Prod.mk_mul_mk, mul_one, one_mul]) (fun z v => hnorm z v)
      a B.e ha hE.1 P B.Re hP.2 hE.2 x y hm
  have hint : Integrable (fun z : B.I.GA => a z.1 * B.e z.2) (B.I.muA B.μf) := ha.mul_prod hE.1
  refine ⟨⟨hint, key⟩, fun T hT => ?_⟩
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [hT.2, key]

theorem comm_of_isOpOf {G L : Type} [MeasurableSpace G] [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    {μ : Measure G} {π : G → (L →L[ℂ] L)} {φ : G → ℂ} {P E : L →L[ℂ] L} (hP : IsOpOf μ π φ P)
    (hE : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ) (hc : ∀ g, E.comp (π g) = (π g).comp E) (y : L) :
    P (E y) = E (P y) := by
  refine ext_inner_left ℂ fun x => ?_
  rw [hP.2 x (E y), ← hE x (P y), hP.2 (E x) y]
  congr 1
  funext g
  congr 1
  have h := congrArg (fun T : L →L[ℂ] L => T y) (hc g)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h, hE]

theorem abstract_count {G H L : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (σ : G → (H →L[ℂ] H)) (π : G → (L →L[ℂ] L)) (w : H)
    (hw : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H))
    (P E : L →L[ℂ] L) (hPP : ∀ y, P (P y) = P y) (hPs : ∀ x y : L, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ)
    (hEE : ∀ y, E (E y) = E y) (hEs : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ)
    (hPE : ∀ y, P (E y) = E (P y)) (hc : ∀ g, E.comp (π g) = (π g).comp E)
    (hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : H →L[ℂ] L, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w)
    (S : Submodule ℂ (H →L[ℂ] L))
    (hS : ∀ A, A ∈ S ↔ ∃ A₀ : H →L[ℂ] L, (∀ g : G, A₀ ∘L σ g = π g ∘L A₀) ∧ E ∘L A₀ = A) :
    IsOrthProjOnto (P.comp E) (LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) ∧
      (∀ A ∈ S, (P.comp E) (A w) = A w) ∧
      (∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y) ∧
      Nonempty (S ≃ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) := by
  have hQQ : ∀ y, P (E (P (E y))) = P (E y) := fun y => by rw [← hPE, hPP, hEE]
  have hSi : ∀ A ∈ S, ∀ g, A ∘L σ g = π g ∘L A := by
    intro A hA g
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    rw [ContinuousLinearMap.comp_assoc, hA₀ g, ← ContinuousLinearMap.comp_assoc, hc g,
      ContinuousLinearMap.comp_assoc]
  have huniq : ∀ A ∈ S, ∀ A' ∈ S, A w = A' w → A = A' := by
    intro A hA A' hA' h
    refine ContinuousLinearMap.ext_on hw ?_
    rintro _ ⟨g, rfl⟩
    have e1 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A hA g)
    have e2 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A' hA' g)
    simp only [ContinuousLinearMap.comp_apply] at e1 e2
    show A (σ g w) = A' (σ g w)
    rw [e1, e2, h]
  have hfix : ∀ A ∈ S, (P.comp E) (A w) = A w := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    obtain ⟨y, hy⟩ := (hr (A₀ w)).2 ⟨A₀, hA₀, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [hEE, hPE, ← hy, hPP]
  have hex : ∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y := by
    intro y hy
    simp only [ContinuousLinearMap.comp_apply] at hy
    obtain ⟨io, hio, hyw⟩ := (hr y).1 ⟨E y, hy⟩
    have hEy : E y = y := by rw [← hy, ← hPE, hEE]
    have hmem : E ∘L io ∈ S := (hS _).2 ⟨io, hio, rfl⟩
    have hval : (E ∘L io) w = y := by rw [ContinuousLinearMap.comp_apply, ← hyw, hEy]
    refine ⟨E ∘L io, ⟨hmem, hval⟩, ?_⟩
    rintro A ⟨hA, hAw⟩
    exact huniq A hA _ hmem (by rw [hAw, hval])
  refine ⟨⟨?_, ?_, rfl⟩, hfix, hex, ?_⟩
  · ext y
    simp only [ContinuousLinearMap.comp_apply]
    exact hQQ y
  · intro x y
    simp only [ContinuousLinearMap.comp_apply]
    rw [hPs, hEs, ← hPE]
  · let f : S →ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L) :=
      { toFun := fun A => ⟨(A : H →L[ℂ] L) w, LinearMap.mem_range.2 ⟨(A : H →L[ℂ] L) w, hfix A A.2⟩⟩
        map_add' := fun A B => Subtype.ext rfl
        map_smul' := fun c A => Subtype.ext rfl }
    have hinj : Function.Injective f := fun A A' h =>
      Subtype.ext (huniq _ A.2 _ A'.2 (congrArg Subtype.val h))
    have hsurj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ (by
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
        exact hQQ z)
      exact ⟨⟨A, hA⟩, Subtype.ext hAw⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem globalProj_holds : GlobalProj := by
  intro B d hd hint
  obtain ⟨hReP, hReC, -⟩ := GlobalTheory.IdemProj.re_orth_proj B
  obtain ⟨hU, -, hF, hnw, hph⟩ := GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree B d hd
  obtain ⟨h1, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : (muInf B.I).IsHaarMeasure := by unfold muInf; infer_instance
  haveI : ∀ v, (muG (B.I.ε v)).IsMulRightInvariant := fun v =>
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ (B.I.ε v) g⟩
  haveI : (muInf B.I).IsMulRightInvariant := by unfold muInf; infer_instance
  let σh : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := hU.1, map_mul' := hU.2.1 }
  let πh : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) :=
    { toFun := fun g => B.R (g, 1), map_one' := h1
      map_mul' := fun a b => by rw [← hmul, Prod.mk_mul_mk, mul_one] }
  have hDne : ((∏ v, d v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
  have hsq : ∀ x y : B.Hs, Integrable (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) (muInf B.I) ∧
      ∫ g, ‖⟪y, σh g x⟫_ℂ‖ ^ 2 ∂(muInf B.I) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / (∏ v, d v) := by
    intro x y
    obtain ⟨hi, he⟩ := hF.2 x y x y
    have hre : ∀ g, RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) = ‖⟪y, σh g x⟫_ℂ‖ ^ 2 := by
      intro g
      rw [RCLike.star_def, RCLike.mul_conj]
      norm_cast
    have hfun : (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) =
        fun g => RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) := funext fun g => (hre g).symm
    rw [hfun]
    refine ⟨hi.re, ?_⟩
    rw [integral_re hi, he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have hc : ((‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v : ℝ) : ℂ) = (‖x‖ : ℂ) ^ 2 * (‖y‖ : ℂ) ^ 2 / ((∏ v, d v : ℝ) : ℂ) := by
      push_cast; ring
    rw [← RCLike.ofReal_re (K := ℂ) (‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v)]
    congr 1
    exact hc.symm
  have hintw : Integrable (fun g => ⟪B.tens B.w, σh g (B.tens B.w)⟫_ℂ) (muInf B.I) := by
    refine Integrable.mono' (hint.norm.const_mul (∏ v, d v)⁻¹)
      (continuous_const.inner (hU.2.2.2 (B.tens B.w))).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    show ‖⟪B.tens B.w, B.σs g (B.tens B.w)⟫_ℂ‖ ≤ (∏ v, d v)⁻¹ * ‖ph B d g‖
    rw [hph g, norm_mul, norm_star, Complex.norm_of_nonneg hF.1.le, ← mul_assoc,
      inv_mul_cancel₀ hF.1.ne', one_mul]
  obtain ⟨-, -, hPA⟩ := projAbs_holds B.I.Ginf (muInf B.I) B.Hs σh (fun g x => hU.2.2.1 g x) hU.2.2.2
    (∏ v, d v) hF.1 hsq (B.tens B.w) hnw hintw
  obtain ⟨⟨P, hP⟩, hPall⟩ := hPA (B.I.L2 B.μf B.fund) πh (fun g x => hnorm _ x)
    (fun x => (hcont x).comp (continuous_id.prodMk continuous_const))
  obtain ⟨hSP, -, -, hrange⟩ := hPall P hP
  have hphG : phG (∏ v, d v) σh (B.tens B.w) = ph B d := funext fun g => (hph g).symm
  have hPop : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) (ph B d) P := by
    refine ⟨by rw [← hphG]; exact hP.1, fun x y => ?_⟩
    rw [hP.2 x y, hphG]
    rfl
  have hPP : ∀ y, P (P y) = P y := fun y => by
    have h := congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hSP.isIdempotentElem.eq
    simpa using h
  have hPs : ∀ x y : B.I.L2 B.μf B.fund, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_left P y x, hSP.isSelfAdjoint.adjoint_eq]
  have hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : B.Hs →L[ℂ] B.I.L2 B.μf B.fund,
      (∀ g : B.I.Ginf, io ∘L B.σs g = B.R (g, 1) ∘L io) ∧ v = io (B.tens B.w) := fun v => by
    have h := Set.ext_iff.1 hrange v
    simp only [SetLike.mem_coe, LinearMap.mem_range, ContinuousLinearMap.coe_coe, Set.mem_setOf_eq] at h
    exact h
  have hS : ∀ A, A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re ↔
      ∃ A₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund, (∀ g : B.I.Ginf, A₀ ∘L B.σs g = B.R (g, 1) ∘L A₀) ∧
        B.Re ∘L A₀ = A := by
    intro A
    simp only [AutInst.eHom, Submodule.mem_map]
    constructor
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
  have hPE : ∀ y, P (B.Re y) = B.Re (P y) := comm_of_isOpOf hPop hReP.2.1 hReC
  have hEE : ∀ y, B.Re (B.Re y) = B.Re y := fun y =>
    congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hReP.1
  have hwd := hF.dense_span_orbit (B.tens B.w) (norm_ne_zero_iff.1 (by rw [hnw]; exact one_ne_zero))
  have hAC := abstract_count B.σs (fun g => B.R (g, 1)) (B.tens B.w) hwd P B.Re hPP hPs hEE hReP.2.1
    hPE hReC hr _ hS
  have hconv := conv_prod B (ph B d) P hint hPop
  refine ⟨hReP, hReC, ⟨P.comp B.Re, hconv.1⟩, fun T hT => ?_⟩
  obtain rfl := hconv.2 T hT
  obtain ⟨h1', h2', h3', ⟨eq⟩⟩ := hAC
  refine ⟨h1', h2', h3', fun hfd => ?_, (LinearEquiv.finrank_eq eq).symm⟩
  haveI := hfd
  exact LinearEquiv.finiteDimensional eq

end GlobalTheory.GlobProj
