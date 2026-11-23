import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def phi0 {D : D7} (X : HidaSetting D) {ι η : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : X.B.I.Ginf :=
  (fun v => expU (X.B.I.ε v) (L p.1 v)) * (fun v => expU (X.B.I.ε v) (L₁ p.2 v))

def GinfDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        MeasurableSet (phi0 X L L₁ '' A) ∧
        Formalism.L2.SG.ProjRows.muInf X.B.I (phi0 X L L₁ '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

theorem grpDens_of (hG : GinfDens) (hU : UnimodInf) : GrpDens := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  obtain ⟨ψ, hT, μinf, νinf, fibInf, hP⟩ := ctx.1
  obtain ⟨hb', FdN, FdN', u, hX⟩ := hP.1
  have hGt : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb) := hX.1.2.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : PolishSpace X.B.I.Ginf := PI.AprimeInfA.polish_of_lcsc _
  have hemb : MeasurableEmbedding (X.toInf hb) :=
    (MassDataMassesW.continuous_toInf X hb).measurableEmbedding (toInf_injective X hb)
  obtain ⟨r, hr, d, hdc, hd0, hd⟩ := hG X u' hb c S L L₁ ctx
  refine ⟨r, hr, d, hdc, hd0, fun A hA hAm => ?_⟩
  obtain ⟨hmeas, heq⟩ := hd A hA hAm
  set k := X.toInf hb c with hk
  set B' := X.toInf hb '' (phi0 X L L₁ '' A) with hB'
  have hB'm : MeasurableSet B' := hemb.measurableSet_image.2 hmeas
  have hpt : ∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η,
      kap0 X hb c L p.1 * chiOf X hb c L₁ p.2 = k * X.toInf hb (phi0 X L L₁ p) * k⁻¹ := by
    intro p
    unfold kap0 chiOf phi0
    change toInfHom X hb _ * toInfHom X hb _ = toInfHom X hb c * toInfHom X hb _ * (toInfHom X hb c)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    group
  have himg : (fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A =
      (fun g => k⁻¹ * g * k) ⁻¹' B' := by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      show k⁻¹ * (kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) * k ∈ B'
      rw [hpt p]
      exact ⟨phi0 X L L₁ p, ⟨p, hp, rfl⟩, by group⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      refine ⟨p, hp, ?_⟩
      show kap0 X hb c L p.1 * chiOf X hb c L₁ p.2 = g
      rw [hpt p, hy]
      group
  have hinv : X.measG.μGinf ((fun g => k⁻¹ * g * k) ⁻¹' B') = X.measG.μGinf B' := by
    have hpm : MeasurableSet ((fun g => k⁻¹ * g * k) ⁻¹' B') :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable hB'm
    calc X.measG.μGinf ((fun g => k⁻¹ * g * k) ⁻¹' B')
        = ∫⁻ g, B'.indicator 1 (k⁻¹ * g * k) ∂X.measG.μGinf := by
          rw [← lintegral_indicator_one hpm]
          rfl
      _ = ∫⁻ g, B'.indicator 1 (k⁻¹ * g) ∂X.measG.μGinf := by
          have := hU X u' ψ hT μinf νinf fibInf hP (fun x => B'.indicator 1 (k⁻¹ * x)) k
          simpa [mul_assoc] using this
      _ = ∫⁻ g, B'.indicator 1 g ∂X.measG.μGinf :=
          lintegral_mul_left_eq_self (fun g => B'.indicator (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) g) k⁻¹
      _ = X.measG.μGinf B' := lintegral_indicator_one hB'm
  rw [himg, hinv, hGt, hemb.map_apply, hB', (toInf_injective X hb).preimage_image, heq]

def PlaceCharts : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η]
    L L₁, @StdCtx D X u' hb c S ι η _ _ L L₁ →
    ∃ (α β : NumberField.InfinitePlace X.B.I.F → Type) (_ : ∀ v, Fintype (α v)) (_ : ∀ v, Fintype (β v))
      (Φ : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) → Formalism.REAL.UJ (X.B.I.ε v))
      (Dv : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) → ℝ)
      (U : ∀ v, Set (EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)))
      (T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ (∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)))
      (r : ℝ),
      (∀ v, MeasurableSet (U v)) ∧ (∀ v, Continuous (Φ v)) ∧ (∀ v, Set.InjOn (Φ v) (U v)) ∧
      (∀ v, Measurable (Dv v)) ∧ (∀ v z, 0 ≤ Dv v z) ∧
      (∀ v, ∀ A ⊆ U v, MeasurableSet A →
        Formalism.REAL.muG (X.B.I.ε v) (Φ v '' A) = ∫⁻ z in A, ENNReal.ofReal (Dv v z)) ∧
      MeasurePreserving T volume (Measure.pi fun v => volume) ∧ Continuous T ∧ 0 < r ∧
      (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, T p ∈ Set.univ.pi U) ∧
      (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, phi0 X L L₁ p = fun v => Φ v (T p v)) ∧
      ContinuousAt (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => ∏ v, Dv v (z v)) (T 0) ∧
      ∏ v, Dv v (T 0 v) = Formalism.MainNotions.S.AutInst.gaugeU X.B.I

theorem ginfDens_of (h : PlaceCharts) : GinfDens := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  obtain ⟨α, β, hα, hβ, Φ, Dv, U, T, r, hUm, hΦc, hΦi, hDm, hD0, hdens, hT, hTc, hr, hTU, hphi, hcont, hval⟩ :=
    h X u' hb c S L L₁ ctx
  have : PolishSpace X.B.I.Ginf := PI.AprimeInfA.polish_of_lcsc _
  refine ⟨r, hr, fun p => ∏ v, Dv v (T p v), ?_, hval, fun A hA hAm => ?_⟩
  · exact ContinuousAt.comp (g := fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => ∏ v, Dv v (z v)) hcont
      hTc.continuousAt
  have himg : phi0 X L L₁ '' A = (fun z v => Φ v (z v)) '' (T '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun p hp => hphi p (hA hp)
  have hTA : MeasurableSet (T '' A) := T.measurableSet_image.2 hAm
  have hTAU : T '' A ⊆ Set.univ.pi U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hTU p (hA hp)
  have hinj : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) (Set.univ.pi U) := by
    intro z hz z' hz' he
    funext v
    exact hΦi v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he v)
  have hcΦ : Continuous (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
    continuous_pi fun v => (hΦc v).comp (continuous_apply v)
  have hmeas : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (T '' A)) :=
    hTA.image_of_continuousOn_injOn hcΦ.continuousOn (hinj.mono hTAU)
  refine ⟨himg ▸ hmeas, ?_⟩
  rw [himg, Formalism.L2.SG.ProjRows.muInf,
    PI.AprimeInfG.pi_chart_dens (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun _ => volume) Φ
      (fun v => (hΦc v).measurable) U hUm hΦi Dv hDm hdens (T '' A) hTAU hTA hmeas,
    ← hT.setLIntegral_comp_emb T.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hD0 v _]

end PI.AprimeInfW
