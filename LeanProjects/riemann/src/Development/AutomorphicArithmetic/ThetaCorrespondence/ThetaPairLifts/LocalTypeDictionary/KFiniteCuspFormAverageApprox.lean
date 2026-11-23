import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgIsCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgIsCuspStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
namespace GlobalTheory.KFinCuspApprox
theorem isCuspForm_kFinite_average : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D)
    (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ →
    IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro D θ hθ _ N τ e he φ hφ hc
  set A : Formalism.REAL.KG (N.M.ε τ) → GA D N.V :=
    fun k => atTau θ N.V τ ((N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ) with hA
  have hAc : Continuous A := (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
    GlobalTheory.SeriesToClosure.continuous_conjK fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hl : LeftInv (GQ N.V) φ := hφ.left
  have havg : ∀ x, GlobalTheory.KFinCuspApprox.avgN θ N τ e φ x = ∫ k, e k * φ (x * A k) ∂(Formalism.REAL.muK (N.M.ε τ)) :=
    fun x => rfl
  have hlA : LeftInv (GQ N.V) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := fun γ hγ g => by
    simp only [havg, mul_assoc, hl γ hγ]
  refine (isCuspFun_iff hlA).2 fun W hW => funext fun x => ?_
  have hcc := cocompact_single hW
  have h0 := congrFun ((isCuspFun_iff hl).1 hc W hW)
  set NN := NA (IsoFlag.single hW) with hNN
  have h𝓕 := isFundamentalDomain_stdDom ((GQ N.V).subgroupOf NN) (Measure.haar : Measure NN)
  have hfin := hcc.measure_ne_top h𝓕
  show constTermOn (GQ N.V) NN _ x = 0
  rw [hcc.constTermOn_eq_zero_iff h𝓕 hlA x]
  have hz : ∀ y, ∫ n in stdDom ((GQ N.V).subgroupOf NN), φ ((n : GA D N.V) * y) ∂(Measure.haar : Measure NN) = 0 :=
    fun y => (hcc.constTermOn_eq_zero_iff h𝓕 hl y).1 (h0 y)
  obtain ⟨K0, hK0, hs⟩ := hcc
  have hcont : Continuous fun p : NN × Formalism.REAL.KG (N.M.ε τ) => φ ((p.1 : GA D N.V) * x * A p.2) :=
    hφ.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hAc.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hK0.prod (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ (n : NN) k, ‖φ ((n : GA D N.V) * x * A k)‖ ≤ C := fun n k => by
    obtain ⟨γ, hγ, hk⟩ := hs n
    have h1 := hC (γ * n, k) ⟨hk, trivial⟩
    have h2 := hl ((γ : NN) : GA D N.V) (Subgroup.mem_subgroupOf.1 hγ) ((n : GA D N.V) * x * A k)
    simp only [Subgroup.coe_mul] at h1
    have e1 : ((γ : NN) : GA D N.V) * n * x * A k = (γ : GA D N.V) * ((n : GA D N.V) * x * A k) := by
      simp only [mul_assoc]
    rwa [e1, h2] at h1
  obtain ⟨Ce, hCe⟩ := (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ))).exists_bound_of_continuousOn he.continuousOn
  haveI : IsFiniteMeasure ((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))) :=
    isFiniteMeasure_restrict.2 hfin
  have hint : Integrable (Function.uncurry fun (n : NN) (k : Formalism.REAL.KG (N.M.ε τ)) => e k * φ ((n : GA D N.V) * x * A k))
      (((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))).prod (Formalism.REAL.muK (N.M.ε τ))) := by
    refine Integrable.mono' (integrable_const (Ce * C)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((he.comp continuous_snd).mul hcont).aestronglyMeasurable
    · show ‖e p.2 * φ ((p.1 : GA D N.V) * x * A p.2)‖ ≤ Ce * C
      rw [norm_mul]
      exact mul_le_mul (hCe p.2 trivial) (hb p.1 p.2) (norm_nonneg _) ((norm_nonneg _).trans (hCe p.2 trivial))
  calc ∫ n in stdDom ((GQ N.V).subgroupOf NN), GlobalTheory.KFinCuspApprox.avgN θ N τ e φ ((n : GA D N.V) * x)
        ∂(Measure.haar : Measure NN)
      = ∫ n in stdDom ((GQ N.V).subgroupOf NN), ∫ k, e k * φ ((n : GA D N.V) * x * A k) ∂(Formalism.REAL.muK (N.M.ε τ))
        ∂(Measure.haar : Measure NN) := by simp only [havg]
    _ = ∫ k, ∫ n in stdDom ((GQ N.V).subgroupOf NN), e k * φ ((n : GA D N.V) * x * A k)
        ∂(Measure.haar : Measure NN) ∂(Formalism.REAL.muK (N.M.ε τ)) := integral_integral_swap hint
    _ = ∫ k, e k * 0 ∂(Formalism.REAL.muK (N.M.ε τ)) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [integral_const_mul, ← hz (x * A k)]
        simp only [mul_assoc]
    _ = 0 := by simp
end GlobalTheory.KFinCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cuspForm_average_approx : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ → IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | exact _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | (intros; apply _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average <;> assumption)
end
