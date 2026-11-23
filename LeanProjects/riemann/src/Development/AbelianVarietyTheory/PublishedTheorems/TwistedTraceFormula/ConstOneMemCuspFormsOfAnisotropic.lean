import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsHaarZetaValueAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open scoped NNReal ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.DblModel

variable {D : D7} {V : HSp D}

theorem const_one_mem_cuspForms_of_anisotropic (h : IsAniso V) (θ : InfF D) (A : CptF V) : (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A :=
  Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem hypotheses_inhabited (D : D7) (n b : ℕ) :
    ∃ (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (θ : InfF D) (A : CptF V) (m : Measure (GA D V)),
      V.rank = n ∧ IsMaj V a ∧ IsHeckeChar D μ ∧ ResEta D μ b ∧ IsInfFam θ ∧ V.SigOK ∧ Cusp.IsCartanFrame V A ∧
        m.IsHaarMeasure ∧ (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let V : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  have h1 : IsHeckeChar D (η ^ b) := ⟨by
    have : ((η ^ b : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ b := by funext x; simp
    rw [this]; exact hη.1.1.pow b, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hr := hη.2.2.1
  have h2 : ResEta D (η ^ b) b := ⟨hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]⟩
  obtain ⟨a, ha⟩ := exists_isMaj V
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hV : V.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨A, hA⟩ := Cusp.exists_isCartanFrame V hV
  exact ⟨V, a, _, θ, A, Measure.haar, rfl, ha, h1, h2, hθ, hV, hA, inferInstance,
    const_one_mem_cuspForms_of_anisotropic (ThetaMean.Model.isAniso_posSpace n) θ A⟩

theorem resEta_one (D : D7) (b : ℕ) : ResEta D 1 (2 * b) := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  exact resEta_parity (n := 0) ⟨hη.2.2.1.1, fun _ _ _ => rfl⟩ (by omega)

theorem exists_regular_one_not_zero (V : HSp D) (s₀ : ℂ) :
    ∃ Φ, EisContinues V Φ ∧ EisRegularAt V Φ s₀ 1 ∧ ¬ EisRegularAt V Φ s₀ 0 := by
  obtain ⟨Φ, h1, h2, -⟩ := Model.exists_family V Measure.haar fun s => (s - s₀)⁻¹
  have h3 : ∀ g, IsMerExt (eisSer V Φ g) univ fun s => (s - s₀)⁻¹ := fun g =>
    ⟨isRightDomain_univ, fun s _ => by fun_prop, 0, fun s _ => (h1 s g).symm⟩
  have hc : EisContinues V Φ := ⟨h2.1, fun g => ⟨_, h3 g⟩⟩
  refine ⟨Φ, hc, ⟨1, fun _ _ => 1, one_pos, fun s _ hs g => ?_, fun _ => differentiableOn_const _, continuousOn_const,
    1, 0, fun _ _ _ => by simp⟩, fun h => ?_⟩
  · have : eisCont V Φ s g = (s - s₀)⁻¹ := (HolValueAt.valueAt ⟨_, (h3 g).isExtAt trivial,
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hs), rfl⟩).cont_eq
    rw [this, pow_one, mul_inv_cancel₀ (sub_ne_zero.2 hs)]
  · obtain ⟨c, hc⟩ := ((h3 1).isExtAt trivial).poleLE_iff.1 ((h.eisPoleLE hc).2 1)
    have h4 : Tendsto (fun s => (s - s₀) * ((s - s₀) ^ 0 * (s - s₀)⁻¹)) (𝓝[≠] s₀) (𝓝 1) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => by simp [sub_ne_zero.2 hs])
    have h5 := ((tendsto_nhdsWithin_of_tendsto_nhds (s := {s₀}ᶜ) (continuous_sub_right s₀).continuousAt.tendsto).mul hc)
    simpa using tendsto_nhds_unique h5 h4

theorem petCoef_one (m : Measure (GA D V)) : petCoef V m 1 1 = fun _ => (((autMeasure V m).real univ : ℝ) : ℂ) := by
  funext g
  simp [petCoef, Cusp.petersson, pet, AutomorphicL2Unitary.descend, rTr]

theorem basicIdentity_value_smul {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} [SigmaFinite m]
    {Φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ} (h : BasicIdentity V μ m Φ f₁ f₂) (c : ℝ≥0) :
    dblInt V μ (c • m) (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) (c • m) Φ (petCoef V (c • m) f₁ f₂) := by
  have e : autMeasure V (c • m) = c • autMeasure V m := quotMeasure_smul (c : ENNReal)
  have e2 : ∀ g, petCoef V (c • m) f₁ f₂ g = (c : ℂ) * petCoef V m f₁ f₂ g := fun g => by
    change ∫ _, _ ∂autMeasure V (c • m) = _
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]; rfl
  rw [dblInt_smul_measure, h.2.2, zetaH_eq, zetaH_eq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    sq, mul_assoc, ← integral_const_mul]
  congr 2
  funext g
  rw [e2, map_mul, Complex.conj_ofReal]
  ring

theorem dblInt_sph_pos (hP : Published.DoublingMethod) (h0 : 0 < V.rank) (hA : IsAniso V) (hV : V.SigOK)
    {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a) (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a))
    (m : Measure (GA D V)) [m.IsHaarMeasure] {σ : ℝ} (hσ : (V.rank : ℝ) / 2 < σ) :
    0 < (dblInt V 1 m (eis V (sph V a σ)) 1 1).re := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, hC⟩ := Cusp.exists_isCartanFrame V hV
  obtain ⟨-, h2, h3⟩ := basicIdentity_of_mem hP h0 ha hI (μ := 1) ⟨continuous_const, fun _ => rfl⟩ (resEta_one D 0)
    (sph_mem hI σ) (by simpa using hσ) hθ hV hC m (const_one_mem_cuspForms_of_anisotropic hA θ A) (const_one_mem_cuspForms_of_anisotropic hA θ A)
  have hv : 0 < (autMeasure V m).real univ :=
    ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  have e : (fun g => sph V a σ (ioH _ D.sp.cm.sig (gram_hdbl V) (g, 1)) * conj (petCoef V m 1 1 g)) = fun g =>
      (((hgt V a (io V (g, 1)) : ℝ) ^ (σ + (V.rank : ℝ) / 2) * (autMeasure V m).real univ : ℝ) : ℂ) := by
    funext g
    rw [petCoef_one, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    push_cast; rfl
  rw [zetaConvH_iff, e] at h2
  rw [h3, zetaH_eq, e, integral_complex_ofReal, Complex.ofReal_re]
  have hp : ∀ g, 0 < (hgt V a (io V (g, 1)) : ℝ) ^ (σ + (V.rank : ℝ) / 2) * (autMeasure V m).real univ := fun g =>
    mul_pos (Real.rpow_pos_of_pos (hgtH_pos _) _) hv
  refine (integral_pos_iff_support_of_nonneg (fun g => (hp g).le) (by simpa using h2.re)).2 ?_
  rw [show Function.support _ = univ from eq_univ_of_forall fun g => (hp g).ne']
  exact isOpen_univ.measure_pos m univ_nonempty

theorem not_basicIdentity_one [Infinite (GQ V)] (m : Measure (GA D V)) [m.IsHaarMeasure] :
    ¬ BasicIdentity V 1 m 1 1 1 := fun b => by
  have hd := isFundamentalDomain_stdDom (GQ V) m
  have h : m univ = ⊤ := by
    rw [hd.measure_eq_tsum univ]
    simp only [smul_set_univ, univ_inter]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (hd.measure_ne_zero (NeZero.ne m))
  have h2 := b.2.1
  rw [zetaConvH_iff, petCoef_one] at h2
  simp only [Pi.one_apply, one_mul, Complex.conj_ofReal] at h2
  rcases integrable_const_iff.1 h2 with h3 | h3
  · exact Model.vol_ne_zero V m h3
  · exact measure_ne_top m _ h

theorem conclusion_zero (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (s₁ s₀ : ℂ)
    (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    EisRegularAt V (flat V a 0 s₁) s₀ 0 ∧ BasicIdentity V μ m (flat V a 0 s₁ s₀) f₁ f₂ := by
  have h1 : flat V a 0 s₁ = fun _ _ => 0 := by
    funext s g
    exact (flatH_apply _ _ _ _).trans (by simp)
  have h2 : eis V (fun _ => 0) = fun _ => 0 := by
    funext g
    simp [eis, cosetSum, term]
  have h3 : dblIntegrandQ V μ (fun _ => 0) f₁ f₂ = fun _ => 0 := funext fun _ => by simp [dblIntegrandQ, dblIntegrand]
  rw [h1]
  refine ⟨⟨1, fun _ _ => 0, one_pos, fun s _ _ g => ?_, fun _ => differentiableOn_const _, continuousOn_const,
    0, 0, fun _ _ _ => by simp⟩, ?_⟩
  · have : eisSer V (fun _ _ => (0 : ℂ)) g = fun _ => 0 := funext fun s => congrFun h2 g
    rw [eisCont, this, (holValueAt_const 0 s).valueAt.cont_eq, mul_zero]
  · simp only [BasicIdentity, h2, DblConv, dblInt, h3, zetaConvH_iff, zetaH_eq, zero_mul, integral_zero,
      integrable_zero, and_true]
    exact ⟨⟨fun _ _ _ => by simp [dblIntegrand], integrable_zero _ _ _⟩, integrable_zero _ _ _⟩

end GlobalTheory.Eis.DblModel

end
