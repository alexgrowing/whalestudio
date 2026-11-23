import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_meanAdm (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) (d : SD σ) :
    ∃ Λ ∈ (adeleClass F).adm d.κ, ∀ Ψ ∈ d.sch,
      Λ Ψ = (d.μ.real d.D)⁻¹ • ∫ g in d.D, thetaSum F (d.S g Ψ) ∂d.μ := by
  obtain ⟨l, hl, hlθ⟩ := exists_lth d
  have hpres : ∀ g, ∀ Ψ ∈ d.sch, d.S g Ψ ∈ d.sch := fun g Ψ hΨ => d.ok.dbl.lin.pres g Ψ hΨ
  have hfun : ∀ Ψ ∈ d.sch, (fun g => l (d.S g Ψ)) = fun g => thetaSum F (d.S g Ψ) :=
    fun Ψ hΨ => funext fun g => hlθ _ (hpres g Ψ hΨ)
  have hint : ∀ Ψ ∈ d.sch, IntegrableOn (fun g => l (d.S g Ψ)) d.D d.μ := fun Ψ hΨ => by
    rw [hfun Ψ hΨ]; exact intOn_S hS hP hT d hΨ
  set c : ℝ := (d.μ.real d.D)⁻¹ with hc
  let L0 : d.sch →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => c • ∫ g in d.D, l (d.S g Ψ.1) ∂d.μ
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, map_add]
        rw [integral_add (hint _ Ψ.2) (hint _ Ψ'.2), smul_add]
      map_smul' := fun a Ψ => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul, mul_smul_comm] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L0
  have hΛv : ∀ Ψ (hΨ : Ψ ∈ d.sch), Λ Ψ = c • ∫ g in d.D, l (d.S g Ψ) ∂d.μ := fun Ψ hΨ => by
    have := congrArg (fun L => L ⟨Ψ, hΨ⟩) hΛ
    simpa [L0] using this
  refine ⟨Λ, fun gf hgf => ?_, fun Ψ hΨ => by rw [hΛv Ψ hΨ, hfun Ψ hΨ]⟩
  choose Th hTh using fun h : UA σ d.A.J => d.ok.dbl.lin.adm h l hl gf hgf
  have hmem : ∀ f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f gf ∈ d.sch :=
    fun f => Submodule.subset_span ⟨f, gf, hgf, rfl⟩
  have hTv : ∀ h f, Th h f = thetaSum F (d.S h (pureA F f gf)) := fun h f => by
    rw [← hTh h f, LinearMap.comp_apply, hlθ _ (hpres h _ (hmem f))]
  haveI : BarrelledSpace ℂ (SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ) := GlobalTheory.T.schwartzMap_barrelledSpace' _
  have hUE : UniformEquicontinuous ((↑) ∘ Th) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun _ f => by
    obtain ⟨C, hC⟩ := bdd_S hS hP hT d (hmem f)
    refine ⟨C, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa [hTv] using hC h
  have hpa : ∀ f f' : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') gf = pureA F f gf + pureA F f' gf := fun f f' => funext fun x => by
    simp [pureA, add_mul]
  have hps : ∀ (a : ℂ) (f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) gf = a • pureA F f gf := fun a f => funext fun x => by
    simp [pureA, mul_assoc]
  let Lf : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ (pureA F f gf)
      map_add' := fun f f' => by rw [hpa, map_add]
      map_smul' := fun a f => by rw [hps, map_smul]; rfl }
  have hLf : ∀ f, Lf f = c • ∫ g in d.D, Th g f ∂d.μ := fun f => by
    show Λ (pureA F f gf) = _
    rw [hΛv _ (hmem f)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show l (d.S g (pureA F f gf)) = Th g f
    rw [← hTh g f]; rfl
  have hfin : d.μ d.D < ⊤ := (cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom
  have hpos : 0 < d.μ.real d.D := by
    haveI := (cpt hS d).cnt
    haveI := d.ok.haar
    exact ENNReal.toReal_pos (fd_ne d.ok.dom) hfin.ne
  have hcont : Continuous Lf := by
    refine continuous_of_continuousAt_zero Lf.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.1 (hUE.equicontinuous 0)) (ε / 2) (half_pos hε)] with f hf
    rw [dist_zero_right]
    show ‖Lf f‖ < ε
    rw [hLf]
    have hb : ∀ g ∈ d.D, ‖Th g f‖ ≤ ε / 2 := fun g _ => by
      have := (hf g).le
      simpa [dist_comm] using this
    calc ‖c • ∫ g in d.D, Th g f ∂d.μ‖ ≤ c * (ε / 2 * d.μ.real d.D) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin hb
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := half_lt_self hε
  exact ⟨⟨Lf, hcont⟩, fun f => rfl⟩

end PositivityTheory.SiegelWeilFormula.Tauto

end
