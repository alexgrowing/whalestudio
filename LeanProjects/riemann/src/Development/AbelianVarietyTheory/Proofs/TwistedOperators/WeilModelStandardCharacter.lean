import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelGoodLineActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer

theorem schwartz_diffQuotient_eval_mul_eq_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (y : κ → mixedEmbedding.mixedSpace F) (R : ℂ) (t : ℝ) :
    (t⁻¹ • (s t - s 0)) y * R = slope (fun t => s t y * R) 0 t := by
  simp only [slope_def_module, sub_zero, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_mul_assoc, sub_mul]

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) {m : ℕ}
    (Φ : Fin m → (Fin n × Fin d → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, Φ i)) = ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (Φ i)) := by
  have hsum : M.co.rho ψ u (∑ i, Φ i) = ∑ i, M.co.rho ψ u (Φ i) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]
  have hmem : ∀ i, M.co.rho ψ u (Φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i => GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u (Φ i) (hΦ i)
  rw [hsum]
  have key := map_sum (GlobalTheory.WeilM.thetaLin F (Fin n × Fin d))
    (fun i => (⟨M.co.rho ψ u (Φ i), hmem i⟩ : GlobalTheory.WeilM.schA F (Fin n × Fin d))) Finset.univ
  simpa only [GlobalTheory.WeilM.thetaLin_apply, Submodule.coe_sum] using key

private theorem hasDerivAt_tens {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (hs : Tendsto (fun t : ℝ => t⁻¹ • (s t - s 0)) (𝓝[≠] 0) (𝓝 g)) (r : (κ → AF F) → ℂ) (x : κ → AF F) :
    HasDerivAt (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑(s t)) r x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑g) r x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont : Continuous fun h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ => h (fun j => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x j)) :=
    ((BoundedContinuousFunction.evalCLM ℂ (fun j => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x j))).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)).continuous
  have hlim := ((hcont.tendsto g).comp hs).mul_const (r x)
  refine hlim.congr' (Filter.Eventually.of_forall fun t => ?_)
  exact schwartz_diffQuotient_eval_mul_eq_slope s _ (r x) t

theorem hasDerivAt_thetaSum_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ m f f₁ φ hφ hD u

  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hR : ∀ i (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑h)
        (fun x => ∏ᶠ v, φ i v fun j => GlobalTheory.AdelicU.evFin F v (x j)) :=
    fun i h => GlobalTheory.ThK.EvUniqInf.rest_pure h (φ i) (hφ i).1 (hstd i)
  have hmem : ∀ i (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := fun i h => (hR i h).2

  choose c g hc hg using fun i =>
    GlobalTheory.T.weil_model_good_line_action hP M ψ χX χW om hCM hψ hM hW γ hγ (f i) (φ i) (hφ i).1 (hφ i).2

  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) := by
    intro i
    funext x
    have h1 := hD i _ (hR i (f i)) x
    have h2 := hasDerivAt_tens (c i) (g i) (hg i)
      (fun x => ∏ᶠ v, φ i v fun j => GlobalTheory.AdelicU.evFin F v (x j)) x
    have h3 : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑(f i))
          (fun x => ∏ᶠ v, φ i v fun j => GlobalTheory.AdelicU.evFin F v (x j))) x) =
        fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑(c i t))
          (fun x => ∏ᶠ v, φ i v fun j => GlobalTheory.AdelicU.evFin F v (x j)) x := by
      funext t
      exact congrFun (hc i t) x
    rw [h3] at h1
    exact h2.unique h1

  choose Λ hΛ using fun i =>
    GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hM u (φ i) (hφ i).1 (hφ i).2
  have hL : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) = ∑ i, Λ i (c i t) := by
    intro t
    rw [map_sum, Finset.sum_congr rfl (fun i _ => hc i t),
      rho_sum M ψ hψ u (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i t) (φ i)) (fun i => hmem i _)]
    exact Finset.sum_congr rfl fun i _ => hΛ i _
  have hT : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) =
      ∑ i, Λ i (g i) := by
    rw [rho_sum M ψ hψ u (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) (fun i => hmem i _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hpure i, hΛ]
  have hi : ∀ i, HasDerivAt (fun t : ℝ => Λ i (c i t)) (Λ i (g i)) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    refine (((Λ i).continuous.tendsto (g i)).comp (hg i)).congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, slope_def_module, sub_zero, map_sub,
      ContinuousLinearMap.map_smul_of_tower]
  rw [hT]
  exact (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hL)

end GlobalTheory.ThetaLineDer
