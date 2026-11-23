import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistributionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaIntAdm

theorem exists_clm_integral {S Ω : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [FirstCountableTopology S] [BarrelledSpace ℂ S] [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → S →L[ℂ] ℂ)
    (hint : ∀ f, Integrable (fun x => T x f) μ) : ∃ L : S →L[ℂ] ℂ, ∀ f, L f = ∫ x, T x f ∂μ := by
  let q : Seminorm ℂ S := Seminorm.of (fun f => ∫ x, ‖T x f‖ ∂μ)
    (fun f g => by
      have hf := (hint f).norm
      have hg := (hint g).norm
      have hfg := (hint (f + g)).norm
      rw [← integral_add hf hg]
      exact integral_mono hfg (hf.add hg) fun x => by simp only [map_add]; exact norm_add_le _ _)
    (fun c f => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [map_smul, norm_mul]))
  have hq : ∀ f, q f = ∫ x, ‖T x f‖ ∂μ := fun f => rfl
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    apply IsSeqClosed.isClosed
    intro y y₀ hy hlim
    have hc : 0 ≤ c := le_trans (apply_nonneg _ _) (hy 0)
    show q y₀ ≤ c
    rw [hq, integral_norm_eq_lintegral_enorm (hint y₀).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal hc
    have hpt : ∀ x, Tendsto (fun n => ‖T x (y n)‖ₑ) atTop (𝓝 ‖T x y₀‖ₑ) := fun x =>
      ((T x).continuous.enorm.continuousAt.tendsto).comp hlim
    calc ∫⁻ x, ‖T x y₀‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖T x (y n)‖ₑ) atTop ∂μ := by
          congr 1; funext x; exact (hpt x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖T x (y n)‖ₑ ∂μ) atTop :=
          lintegral_liminf_le' fun n => (hint (y n)).aestronglyMeasurable.enorm
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal c) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          show ∫⁻ x, ‖T x (y n)‖ₑ ∂μ ≤ ENNReal.ofReal c
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint (y n))]
          exact ENNReal.ofReal_le_ofReal (hy n)
      _ = ENNReal.ofReal c := liminf_const _
  have hqc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous _ hlsc
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, T x f ∂μ
      map_add' := fun f g => by simp only [map_add]; exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; exact integral_const_mul c _ }
  have hL0 : ContinuousAt L 0 := by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm (a := fun f => q f) (fun f => ?_) ?_
    · exact norm_integral_le_integral_norm _
    · have := hqc.tendsto 0
      rwa [map_zero] at this
  exact ⟨⟨L, continuous_of_continuousAt_zero L.toAddMonoidHom hL0⟩, fun f => rfl⟩

end GlobalTheory.ThetaIntAdm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (theta)
open scoped Classical

theorem GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  intro F E _ _ _ _ _ σ n d X Y M ψ χX χY om hW hC
  obtain ⟨l₀, hl₀, hl₀e⟩ := GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F (Fin n × Fin d)
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  have pres : ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om p Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    hS.pres
  have adm : ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d),
      l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := hS.adm
  have th : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), ∀ g, theta om Φ g 1 = l₀ (om (g, 1) Φ) :=
    fun Φ hΦ g => (hl₀e _ (pres _ Φ hΦ)).symm
  let fI : GlobalTheory.WeilM.schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => M.I om Φ.1 1
      map_add' := fun Φ Ψ => by
        have e : (fun g => theta om (Φ + Ψ).1 g 1) = fun g => theta om Φ.1 g 1 + theta om Ψ.1 g 1 := by
          funext g
          rw [th _ (Φ + Ψ).2, th _ Φ.2, th _ Ψ.2, Submodule.coe_add, map_add, map_add]
        show ∫ g in M.dom, theta om (Φ + Ψ).1 g 1 ∂M.μ = ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ + ∫ g in M.dom, theta om Ψ.1 g 1 ∂M.μ
        rw [e]
        exact integral_add (hC _ Φ.2 1) (hC _ Ψ.2 1)
      map_smul' := fun c Φ => by
        have e : (fun g => theta om (c • Φ).1 g 1) = fun g => c * theta om Φ.1 g 1 := by
          funext g
          rw [th _ (c • Φ).2, th _ Φ.2, Submodule.coe_smul, map_smul, map_smul, smul_eq_mul]
        show ∫ g in M.dom, theta om (c • Φ).1 g 1 ∂M.μ = c • ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ
        rw [e, smul_eq_mul]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend fI
  have hlΦ : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 :=
    fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, hlΦ⟩
  intro g₀ hg₀
  have mem : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, GlobalTheory.WeilM.pureA F f g₀ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f => Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  choose T hT using fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J => adm (x, 1) l₀ hl₀ g₀ hg₀
  have eT : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, (fun x => T x f) = fun x => theta om (GlobalTheory.WeilM.pureA F f g₀) x 1 := fun f => by
    funext x
    rw [← hT x f, th _ (mem f)]
    rfl
  haveI := GlobalTheory.T.schwartzMap_barrelledSpace' (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral (M.μ.restrict M.dom) T
    (fun f => by rw [eT f]; exact hC _ (mem f) 1)
  refine ⟨L, fun f => ?_⟩
  rw [hlΦ _ (mem f), hL, eT f]
  rfl
