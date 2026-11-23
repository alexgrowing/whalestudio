import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomialStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ThetaLieInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem I_smul (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, thetaSum_smul]
  exact integral_const_mul _ _

theorem I_add (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (cΦ : M.Conv om Φ) (cΨ : M.Conv om Ψ) (h : UA σ W.J) :
    M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  have hs := hp.weil.isUSplitting.pres
  have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hs _ _ hΦ) (hs _ _ hΨ)
  simp only [Model.I, e]
  exact integral_add (cΦ h) (cΨ h)

theorem exists_deriv_I_eq_zero (hK : KP) (hp : IsPair B M χX χW om r s r' s')
    (hw : d + 2 * min r s < 2 * n ∨ min r s = 0) {γ : Multiplicative ℝ →* UA σ X.J} (hγ : γ ∈ Lines σ X)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Ψ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Ψ x) 0) ∧
      M.I om Ψ = 0 := by
  obtain ⟨hconv, hcont⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B n d X W M χX χW om r s r' s' hp hw
  induction hΦ using Submodule.span_induction with
  | mem Φ hx =>
    obtain ⟨f, φ, hφ, rfl⟩ := hx
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) := fun u =>
      Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    let ρ : (Fin n × Fin d → AF F) → ℂ := fun x => φ fun i => (x i).2
    have htens : ∀ u : SInf F (Fin n × Fin d), tens (evI F) u ρ = pureA F u φ := fun u => rfl
    have hrest : Rest (evI F) f ρ := by
      refine ⟨fun x z hz => ?_, hmem f⟩
      have h0 : evI F ((0, 1) : AF F) = 0 := map_zero _
      have hz2 : ∀ i, (z i).2 = 0 := fun i => by
        have := congrArg (fun y : Fin n × Fin d → AF F => (y i).2) (hz _ h0)
        exact (one_mul _).symm.trans this
      show φ (fun i => (x i).2 + (z i).2) = φ fun i => (x i).2
      simp only [hz2, add_zero]
    obtain ⟨c, g, hc, hlim⟩ := GlobalTheory.T.weil_line_good_model_polynomial hK.base M B.ψ χX χW om hp.base.std hp.good hp.weil γ hγ f ρ hrest
    simp only [htens] at hc
    have hq : ∀ t : ℝ, pureA F ⇑(t⁻¹ • (c t - c 0)) φ =
        ((t⁻¹ : ℝ) : ℂ) • (pureA F (c t) φ + (-1 : ℂ) • pureA F (c 0) φ) := fun t => by
      funext x
      simp only [pureA, SchwartzMap.smul_apply, SchwartzMap.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        Complex.real_smul]
      ring
    refine ⟨pureA F g φ, hmem g, fun x => ?_, funext fun h => ?_⟩
    · simp only [hc]
      rw [hasDerivAt_iff_tendsto_slope]
      let y : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i)
      have hev : Continuous fun u : SInf F (Fin n × Fin d) => pureA F u φ x := by
        classical
        have h1 : Continuous fun u : SInf F (Fin n × Fin d) => u y :=
          (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ).continuous
        exact h1.mul continuous_const
      refine ((hev.tendsto g).comp hlim).congr fun t => ?_
      simp only [Function.comp_apply, hq, slope_def_module, sub_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        Complex.real_smul]
      ring
    · have hI : ∀ t : ℝ, M.I om (pureA F (c t) φ) h = M.I om (pureA F f φ) h := fun t => by
        rw [← hc t, GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp _ _ (hmem f)]
      have h0 : ∀ t : ℝ, M.I om (pureA F ⇑(t⁻¹ • (c t - c 0)) φ) h = 0 := fun t => by
        have hm := Submodule.smul_mem _ (-1 : ℂ) (hmem (c 0))
        rw [hq, I_smul, I_add hp (hmem _) hm (hconv _ (hmem _)).1 (hconv _ hm).1, I_smul, hI, hI]
        ring
      have h1 := ((hcont φ hφ h).tendsto g).comp hlim
      have h2 : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[≠] 0) (𝓝 (M.I om (pureA F g φ) h)) := h1.congr h0
      exact tendsto_nhds_unique h2 tendsto_const_nhds
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, funext fun h => ?_⟩
    · simpa only [map_zero, Pi.zero_apply] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simpa using I_smul (M := M) (om := om) 0 0 h
  | add Φ Φ' _ _ ih ih' =>
    obtain ⟨Ψ, hΨ, hd, hI⟩ := ih
    obtain ⟨Ψ', hΨ', hd', hI'⟩ := ih'
    refine ⟨Ψ + Ψ', Submodule.add_mem _ hΨ hΨ', fun x => ?_, funext fun h => ?_⟩
    · simpa only [map_add, Pi.add_apply] using (hd x).fun_add (hd' x)
    · rw [I_add hp hΨ hΨ' (hconv _ hΨ).1 (hconv _ hΨ').1, hI, hI']
      simp
  | smul a Φ _ ih =>
    obtain ⟨Ψ, hΨ, hd, hI⟩ := ih
    refine ⟨a • Ψ, Submodule.smul_mem _ a hΨ, fun x => ?_, funext fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (hd x).const_mul a
    · rw [I_smul, hI]
      simp

theorem thetaIntegral_lie_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → G.M.I om Φ₁ = 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm γ hγ Φ hΦ Φ₁ _ hd
  have hp := GlobalTheory.ThK.Inhab.pairV hm.triple
  have hPol : PolData B G.M ≤ schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hp.good.std).mono fun v hv => hv.1.trans hv.2)
  have hw : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
    have h1 := hm.triple.geo.eBig
    have h2 := min_le_right (a - G.p) G.p
    omega
  obtain ⟨Ψ, -, hΨ, hI⟩ := exists_deriv_I_eq_zero hK hp (Or.inl hw) hγ (hPol hΦ)
  rw [show Φ₁ = Ψ from funext fun x => (hd x).unique (hΨ x), hI]

end GlobalTheory.ThetaLieInt

end
