import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLawsStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.FlatForm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem enorm_psi (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, hψ.1.2.1 a, ENNReal.ofReal_one]

section
variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
  {μS : Measure (Mx D W.rank ρ)} {𝓕S : Set (Mx D W.rank ρ)} {μT : Measure (Mx D σ V₀.rank)} {𝓕T : Set (Mx D σ V₀.rank)}

theorem enorm_evalAt_le (hψ : IsStdChar D ψ (-1)) (hT : μT 𝓕T = 1) (f : WO V W → ℂ) (x : Mx D W.rank ρ) (M : ℝ≥0∞)
    (hM : ∀ w', ‖dV.mixS W ψ μS 𝓕S f x w'‖ₑ ≤ M) (y : Mx D V₀.rank σ) (w : WO V₀ W₀) :
    ‖evalAt ψ dV dW μS 𝓕S μT 𝓕T f x y w‖ₑ ≤ M := by
  unfold evalAt HypDec.mixT
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono (g := fun _ => M) fun ξ => ?_).trans (le_of_eq ?_))
  · rw [HypDec.integrandT_eq, enorm_mul, enorm_psi hψ, one_mul]; exact hM _
  · rw [setLIntegral_const, hT, mul_one]

theorem enorm_flatFun_le (hψ : IsStdChar D ψ (-1)) (hT : μT 𝓕T = 1) (f : WO V W → ℂ) (x : Mx D W.rank ρ)
    (M : Mx D W.rank ρ → ℝ≥0∞) (hM : ∀ x' w', ‖dV.mixS W ψ μS 𝓕S f x' w'‖ₑ ≤ M x') (y : Mx D V₀.rank σ)
    (w : WO V₀ W₀) (u : UX D ρ) :
    ‖flatFun ψ dV dW μS 𝓕S μT 𝓕T x y f w u‖ₑ ≤ M (x ⬝ u.1.1) := by
  unfold flatFun
  rw [enorm_mul, show ‖star (psiUni ψ u.1)‖ₑ = 1 by
    rw [← ofReal_norm_eq_enorm, norm_star, psiUni, psiE, hψ.1.2.1, ENNReal.ofReal_one], one_mul]
  exact enorm_evalAt_le dV dW hψ hT f _ _ (hM _) y w

end

end GlobalTheory.Unf.FlatForm

namespace GlobalTheory.Unf.FlatForm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section
variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
  {μS : Measure (Mx D W.rank ρ)} {𝓕S : Set (Mx D W.rank ρ)} {μT : Measure (Mx D σ V₀.rank)} {𝓕T : Set (Mx D σ V₀.rank)}

theorem integrable_integrandT (hψ : IsStdChar D ψ (-1)) (hT : μT 𝓕T = 1) (g : WO V₀ W → ℂ) (B : ℝ)
    (hB : ∀ w', ‖g w'‖ ≤ B) (hg : Continuous g) (y : Mx D V₀.rank σ) (w : WO V₀ W₀) :
    Integrable (fun ξ => ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
      g (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)) (μT.restrict 𝓕T) := by
  haveI : BorelSpace (Mx D σ V₀.rank) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μT.restrict 𝓕T) := ⟨by rw [Measure.restrict_apply_univ, hT]; exact ENNReal.one_lt_top⟩
  have hcX : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have hc : Continuous fun ξ : Mx D σ V₀.rank => ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
      g (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w) :=
    (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH hcX continuous_const)).mul
      (hg.comp ((hcX.add continuous_const).add continuous_const))
  refine Integrable.mono' (integrable_const B) hc.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [norm_mul, hψ.1.2.1, one_mul]; exact hB _

theorem continuous_evalAt (hψ : IsStdChar D ψ (-1)) (hT : μT 𝓕T = 1) (f : WO V W → ℂ) (B : ℝ)
    (hB : ∀ x w', ‖dV.mixS W ψ μS 𝓕S f x w'‖ ≤ B)
    (hc : Continuous fun p : Mx D W.rank ρ × WO V₀ W => dV.mixS W ψ μS 𝓕S f p.1 p.2) (y : Mx D V₀.rank σ)
    (w : WO V₀ W₀) : Continuous fun x => evalAt ψ dV dW μS 𝓕S μT 𝓕T f x y w := by
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D W.rank ρ) := inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin ρ → AE D))
  haveI : FirstCountableTopology (Mx D W.rank ρ) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D σ V₀.rank) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μT.restrict 𝓕T) := ⟨by rw [Measure.restrict_apply_univ, hT]; exact ENNReal.one_lt_top⟩
  have hcX : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have hj : Continuous (Function.uncurry fun (x : Mx D W.rank ρ) (ξ : Mx D σ V₀.rank) =>
      ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
        dV.mixS W ψ μS 𝓕S f x (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)) :=
    (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hcX.comp continuous_snd) continuous_const)).mul
      (Continuous.comp (g := fun q : Mx D W.rank ρ × WO V₀ W => dV.mixS W ψ μS 𝓕S f q.1 q.2)
        (f := fun p : Mx D W.rank ρ × Mx D σ V₀.rank => (p.1, dW.incX V₀ p.2 + dW.incAdj V₀ y + dW.inc0 V₀ w)) hc
        (continuous_fst.prodMk (((hcX.comp continuous_snd).add continuous_const).add continuous_const)))
  unfold evalAt HypDec.mixT
  simp only [HypDec.integrandT_eq]
  refine continuous_of_dominated (bound := fun _ => B)
    (fun x => (hj.uncurry_left x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun ξ => ?_) (integrable_const B)
    (ae_of_all _ fun ξ => hj.uncurry_right ξ)
  rw [norm_mul, hψ.1.2.1, one_mul]; exact hB _ _

theorem continuous_upSum : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold upSum
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true]; exact (continuous_apply j).comp ((continuous_apply i).comp hval)
  · simp only [h, if_false]; exact continuous_const

theorem continuous_flatFun (hψ : IsStdChar D ψ (-1)) (f : WO V W → ℂ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)
    (w : WO V₀ W₀) (hc : Continuous fun x' => evalAt ψ dV dW μS 𝓕S μT 𝓕T f x' y w) :
    Continuous (flatFun ψ dV dW μS 𝓕S μT 𝓕T x y f w) := by
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    Units.continuous_val.comp continuous_subtype_val
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  unfold flatFun psiUni psiE
  exact (continuous_star.comp (hψ.1.1.comp (ht.comp continuous_upSum))).mul
    (hc.comp (continuous_const.matrix_mul hval))

end

end GlobalTheory.Unf.FlatForm

namespace GlobalTheory.Unf.FlatForm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section
variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
  {μS : Measure (Mx D W.rank ρ)} {𝓕S : Set (Mx D W.rank ρ)} {μT : Measure (Mx D σ V₀.rank)} {𝓕T : Set (Mx D σ V₀.rank)}

theorem mixS_add (hψ : IsStdChar D ψ (-1)) (hS : IsCovolOne (ratMx D W.rank ρ) μS 𝓕S) {f g : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ) :
    dV.mixS W ψ μS 𝓕S (f + g) x = dV.mixS W ψ μS 𝓕S f x + dV.mixS W ψ μS 𝓕S g x := by
  funext w'
  have h1 := dV.integrableOn_mixS hψ.1.1 hS hf x w'
  have h2 := dV.integrableOn_mixS hψ.1.1 hS hg x w'
  simp only [HypDec.integrandS_eq] at h1 h2
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add]
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO V W → ℂ) (x : Mx D W.rank ρ) :
    dV.mixS W ψ μS 𝓕S (c • f) x = c • dV.mixS W ψ μS 𝓕S f x := by
  funext w'
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a; ring

theorem mixT_add (g₁ g₂ : WO V₀ W → ℂ) (y : Mx D V₀.rank σ) (w : WO V₀ W₀)
    (h₁ : Integrable (fun ξ => ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
      g₁ (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)) (μT.restrict 𝓕T))
    (h₂ : Integrable (fun ξ => ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
      g₂ (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)) (μT.restrict 𝓕T)) :
    dW.mixT V₀ ψ μT 𝓕T (g₁ + g₂) y w = dW.mixT V₀ ψ μT 𝓕T g₁ y w + dW.mixT V₀ ψ μT 𝓕T g₂ y w := by
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.add_apply, mul_add]
  exact integral_add h₁ h₂

theorem mixT_smul (c : ℂ) (g : WO V₀ W → ℂ) (y : Mx D V₀.rank σ) (w : WO V₀ W₀) :
    dW.mixT V₀ ψ μT 𝓕T (c • g) y w = c * dW.mixT V₀ ψ μT 𝓕T g y w := by
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a; ring

end

theorem mixS_bounded (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) {V V₀ W : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (vS : VolM D W.rank ρ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ∃ B : ℝ, ∀ x w', ‖dV.mixS W ψ vS.μ vS.𝓕 f x w'‖ ≤ B := by
  obtain ⟨U, hU, hfix⟩ := hf.level
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hψ θ hθ V V₀ W ρ dV vS U hU
  obtain ⟨C, hC⟩ := hK 0
  have hfin := (GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ V W).1 0 f hf
  have hmem : f ∈ GlobalTheory.Size.thetaLevel ψ V W U := ⟨hf, hfix⟩
  refine ⟨(C * supSob ψ θ 0 f).toReal, fun x w' => ?_⟩
  have hm : ENNReal.ofReal (maj θ K 0 x) ≤ 1 := by
    unfold maj; split_ifs <;> simp
  have h2 : ‖dV.mixS W ψ vS.μ vS.𝓕 f x w'‖ₑ ≤ C * supSob ψ θ 0 f :=
    (hC f hmem x w').trans (by
      calc (↑C * supSob ψ θ 0 f) * ENNReal.ofReal (maj θ K 0 x) ≤ (↑C * supSob ψ θ 0 f) * 1 := by gcongr
        _ = _ := mul_one _)
  rw [← ofReal_norm_eq_enorm] at h2
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).1 h2

end GlobalTheory.Unf.FlatForm

namespace GlobalTheory.Unf.FlatForm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem lintegral_flatFun_le (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ)
    (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose) (y : Mx D V₀.rank σ)
    (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ (N : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ V W U, ∀ w,
      ∫⁻ u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y f w u‖ₑ ∂vU.ν ≤ C * supSob ψ θ N f := by
  obtain ⟨K, hK, hKC⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hψ θ hθ V V₀ W ρ dV vS U hU
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular D θ hθ W.rank ρ vU x hx
  obtain ⟨C, hC⟩ := hKC N
  have hI := hN K hK
  have hIfin : ∫⁻ u, ENNReal.ofReal (maj θ K N ((rat x : Mx D W.rank ρ) ⬝ u.1.1)) ∂vU.ν ≠ ⊤ :=
    hI.lintegral_lt_top.ne
  refine ⟨N, C * (∫⁻ u, ENNReal.ofReal (maj θ K N ((rat x : Mx D W.rank ρ) ⬝ u.1.1)) ∂vU.ν).toNNReal,
    fun f hf w => ?_⟩
  calc ∫⁻ u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y f w u‖ₑ ∂vU.ν
      ≤ ∫⁻ u, (↑C * supSob ψ θ N f) * ENNReal.ofReal (maj θ K N ((rat x : Mx D W.rank ρ) ⬝ u.1.1)) ∂vU.ν :=
        lintegral_mono fun u => enorm_flatFun_le dV dW hψ vT.covol.2.2 f (rat x)
          (fun x' => ↑C * supSob ψ θ N f * ENNReal.ofReal (maj θ K N x')) (hC f hf) y w u
    _ = (↑C * supSob ψ θ N f) * ∫⁻ u, ENNReal.ofReal (maj θ K N ((rat x : Mx D W.rank ρ) ⬝ u.1.1)) ∂vU.ν :=
        lintegral_const_mul'' _ hI.1.aemeasurable.ennreal_ofReal
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hIfin]; ring

theorem flatAt_isSobForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ y : Mx D V₀.rank σ, (∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ w, Integrable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν) ∧ ∀ w, IsSobForm ψ θ V W fun Ψ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y Ψ w := by
  intro D ψ hψ θ hθ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y
  have hT := vT.covol.2.2
  have hS := vS.covol
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∃ B : ℝ, ∀ x' w', ‖dV.mixS W ψ vS.μ vS.𝓕 Ψ x' w'‖ ≤ B :=
    fun Ψ hΨ => mixS_bounded hψ hθ dV vS hΨ
  have hc : ∀ Ψ, IsThetaFunO ψ V W Ψ →
      Continuous fun p : Mx D W.rank ρ × WO V₀ W => dV.mixS W ψ vS.μ vS.𝓕 Ψ p.1 p.2 :=
    fun Ψ hΨ => (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS Ψ hΨ).2.2.2.1
  have hmeas : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ w,
      AEStronglyMeasurable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν := by
    intro Ψ hΨ w
    obtain ⟨B, hB'⟩ := hB Ψ hΨ
    exact (continuous_flatFun dV dW hψ Ψ (rat x) y w
      (continuous_evalAt dV dW hψ hT Ψ B hB' (hc Ψ hΨ) y w)).aestronglyMeasurable
  have hint : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ w,
      Integrable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν := by
    intro Ψ hΨ w
    obtain ⟨U, hU, hfix⟩ := hΨ.level
    obtain ⟨N, C, hb⟩ := lintegral_flatFun_le hψ hθ dV dW vS vT vU x hx y U hU
    exact ⟨hmeas Ψ hΨ w, (hb Ψ ⟨hΨ, hfix⟩ w).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ((GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ V W).1 N Ψ hΨ).lt_top)⟩

  have hTint : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ x' w,
      Integrable (fun ξ => ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ y)) *
        dV.mixS W ψ vS.μ vS.𝓕 Ψ x' (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)) (vT.μ.restrict vT.𝓕) := by
    intro Ψ hΨ x' w
    obtain ⟨B, hB'⟩ := hB Ψ hΨ
    exact integrable_integrandT dW hψ hT _ B (hB' x')
      (Continuous.uncurry_left (f := fun a b => dV.mixS W ψ vS.μ vS.𝓕 Ψ a b) x' (hc Ψ hΨ)) y w
  have hadd : ∀ f g, IsThetaFunO ψ V W f → IsThetaFunO ψ V W g → ∀ w u,
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (f + g) w u =
        flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y f w u + flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y g w u := by
    intro f g hf hg w u
    simp only [flatFun, evalAt]
    rw [mixS_add dV hψ hS hf hg, mixT_add dW _ _ y w (hTint f hf _ w) (hTint g hg _ w), mul_add]
  have hsmul : ∀ (c : ℂ) f w u,
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (c • f) w u =
        c * flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y f w u := by
    intro c f w u
    simp only [flatFun, evalAt]
    rw [mixS_smul dV c f, mixT_smul dW c _ y w]; ring
  refine ⟨hint, fun w => ⟨fun f g hf hg => ?_, fun c f hf => ?_, fun U hU => ?_⟩⟩
  · simp only [flatAt]
    simp_rw [hadd f g hf hg w]
    exact integral_add (hint f hf w) (hint g hg w)
  · simp only [flatAt]
    simp_rw [hsmul c f w]
    exact integral_const_mul c _
  · obtain ⟨N, C, hb⟩ := lintegral_flatFun_le hψ hθ dV dW vS vT vU x hx y U hU
    exact ⟨N, C, fun f hf => (enorm_integral_le_lintegral_enorm _).trans (hb f hf w)⟩

end GlobalTheory.Unf.FlatForm

end
