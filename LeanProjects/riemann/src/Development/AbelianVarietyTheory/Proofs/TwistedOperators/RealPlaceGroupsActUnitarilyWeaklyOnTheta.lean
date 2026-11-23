import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ThetaL2InnerProduct

open GlobalTheory.OrientedHeis GlobalTheory.Size Filter
open scoped Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem ipTh_eq (f f' : WO S T → ℂ) : ipTh μ 𝓕 f f' = GlobalTheory.Ker.ipO μ 𝓕 f f' := rfl

theorem bound_near (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) : ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ w, ‖ω p f w‖ ≤ C := by
  obtain ⟨K, hK, hKγ⟩ := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.2
  have hcont : Continuous fun q : (GA D S × GA D T) × WO S T => ω q.1 f q.2 :=
    GlobalTheory.ThetaJointCont.continuous_om_oriented hω hf
  have hc0 : ContinuousOn (fun w : WO S T => ω p₀ f w) K :=
    (hcont.comp (by fun_prop : Continuous fun w : WO S T => (p₀, w))).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc0
  refine ⟨M + 1, ?_⟩
  have hev : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖ω p f y‖ < M + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hlt : ‖ω p₀ f y‖ < M + 1 := lt_of_le_of_lt (hM y hy) (lt_add_one M)
    exact hcont.norm.continuousAt.eventually_lt continuousAt_const hlt
  filter_upwards [hev] with p hp w
  obtain ⟨γ, hγ, hγK⟩ := hKγ w
  rw [← theta_norm_periodic hω.std (hω.om_pres p f hf) γ hγ w]
  exact (hp _ hγK).le

theorem continuousOn_ip (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    {γ : X → GA D S × GA D T} {U : Set X} (hγ : ContinuousOn γ U) {F E : WO S T → ℂ}
    (hF : IsThetaFunO ψ S T F) (hE : IsThetaFunO ψ S T E) :
    ContinuousOn (fun x => ipTh μ 𝓕 (ω (γ x) F) E) U := by
  intro x₀ hx₀
  obtain ⟨C, hC⟩ := bound_near hω hF (γ x₀)
  obtain ⟨CE, hCE⟩ := theta_bounded hω.std hE
  have hfin : μ 𝓕 ≠ ⊤ := (measure_dom hμ h𝓕).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  unfold ipTh
  refine continuousWithinAt_of_dominated (bound := fun _ => C * CE) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (integrableOn_mul_conj hω.std hμ h𝓕 (hω.om_pres (γ x) F hF) hE).aestronglyMeasurable
  · have ht : Tendsto γ (𝓝[U] x₀) (𝓝 (γ x₀)) := hγ x₀ hx₀
    filter_upwards [ht.eventually hC] with x hx
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hx w) (hCE w) (norm_nonneg _) ((norm_nonneg _).trans (hx w))
  · refine Filter.Eventually.of_forall fun w => ?_
    exact ((hω.om_cont F hF w).continuousAt.comp_continuousWithinAt (hγ x₀ hx₀)).mul continuousWithinAt_const

theorem weaklyContinuous_unitaryAction_of_realUnitaryHom (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} {ι : Type} (G : Mn n) (γ : Mn n → GA D S × GA D T)
    (h1 : γ 1 = 1) (hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, γ (g * g') = γ g * γ g')
    (hc : ContinuousOn γ (Formalism.QuantumDeterminants.UH G)) (pt : MvPolynomial ι ℂ →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (hd : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P, ∃ F', DerAll ψ ω (fun t => γ (NormedSpace.exp (t • X))) (pt P) F') :
    L2UnitaryRepresentationData G (fun g F => ω (γ g) F) pt (ipTh μ 𝓕) (thetaSpace ψ S T) where
  mem := hpt
  pt_lin := fun z P Q => by rw [map_add, map_smul]
  ip_lin := fun z F hF F' hF' E hE => by
    rw [ipTh_eq, ipTh_eq, ipTh_eq, ipO_add_left hω.std hμ h𝓕 (theta_smul z hF) hF' hE, ipO_smul_left]
  ip_symm := fun F _ E _ => by rw [ipTh_eq, ipTh_eq, ipO_conj]
  ip_pos := fun F hF hne => by
    have hc : Continuous F := by
      have h1 : Continuous fun w : WO S T => ω 1 F w :=
        (GlobalTheory.ThetaJointCont.continuous_om_oriented hω hF).comp
          (by fun_prop : Continuous fun w : WO S T => ((1 : GA D S × GA D T), w))
      simpa only [map_one, Module.End.one_apply] using h1
    have h0 : GlobalTheory.Ker.ipO μ 𝓕 F F ≠ 0 := fun h => hne ((ipO_self_eq_zero_iff hω.std hμ h𝓕 hF).1 h)
    rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc] at h0
    rw [ipTh_eq, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc, Complex.ofReal_re]
    exact lt_of_le_of_ne (sq_nonneg _) (fun h => h0 (by rw [← h]; simp))
  stable := fun g _ F hF => hω.om_pres _ F hF
  lin := fun g _ z F _ F' _ => by simp only [map_add, map_smul]
  one := fun F _ => by
    show ω (γ 1) F = F
    rw [h1, map_one]
    rfl
  mul := fun g hg g' hg' F _ => by
    show ω (γ (g * g')) F = ω (γ g) (ω (γ g') F)
    rw [hmul g hg g' hg', map_mul]
    rfl
  unit := fun g _ F hF E hE => by
    show ipTh μ 𝓕 (ω (γ g) F) (ω (γ g) E) = ipTh μ 𝓕 F E
    rw [ipTh_eq, ipTh_eq, ipO_om hω hμ h𝓕 hF hE]
  cont := fun F hF E hE => by
    haveI : FirstCountableTopology (Mn n) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
    exact continuousOn_ip hω hμ h𝓕 hc hF hE
  der := fun X hX P P' hPP' E hE => by
    obtain ⟨F', hF'1, hF'2⟩ := hd X hX P
    have heq : F' = pt P' := by
      funext z
      have hz := hF'1 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at hz
      exact hz.unique (hPP' z)
    have hder := hF'2 μ 𝓕 hμ h𝓕 E hE
    rw [heq] at hder
    exact hder

theorem exists_l2_unitary_theta_of_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  intro D ψ θ S T χS χT ω τ hθ hω frS εS frT εT aS aT pt hpt hL μ 𝓕 hμ h𝓕
  refine ⟨thetaSpace ψ S T, ?_, ?_⟩
  · have hcS := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ S τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D S τ) (fun g => (atTau θ S τ g, (1 : GA D T)))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ]; rfl)
      (fun g hg g' hg' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hg hg', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun X hX P => ⟨_, hL.1 X hX P⟩)
  · have hcT := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D T τ) (fun h => ((1 : GA D S), atTau θ T τ h))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ]; rfl)
      (fun h hh h' hh' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hh hh', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun Y hY P => ⟨_, hL.2 Y hY P⟩)

end GlobalTheory.ThetaL2InnerProduct

end
