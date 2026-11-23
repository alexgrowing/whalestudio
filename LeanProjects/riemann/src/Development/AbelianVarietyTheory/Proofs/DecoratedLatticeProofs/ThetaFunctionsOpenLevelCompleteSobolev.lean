import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnifStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimitsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaWordLimitsSmoothAlongRealPointsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaComplete

theorem lim_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f : WO S T → ℂ, TendstoUniformly u f Filter.atTop → (∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) ∧ (∀ x ∈ U, x.map (infPart D) = 0 → heisO ψ S T x f = f) ∧ Continuous f := by
  intro D ψ S T U u hu f hf
  have ht : ∀ w, Filter.Tendsto (fun j => u j w) Filter.atTop (nhds (f w)) := fun w => hf.tendsto_at w
  refine ⟨fun γ w => ?_, fun x hx h0 => ?_, hf.continuous (Filter.Frequently.of_forall fun j => (hu j).1.cont)⟩
  · refine tendsto_nhds_unique (ht _) ?_
    have e : (fun j => u j (ratW T S γ + w)) = fun j => ψ (-(symplOH S T (ratW T S γ) w)) * u j w :=
      funext fun j => (hu j).1.quasi γ w
    rw [e]
    exact (ht w).const_mul _
  · funext w
    refine tendsto_nhds_unique ((ht (w + x)).const_mul (ψ (symplOH S T w x))) ?_
    have e : (fun j => ψ (symplOH S T w x) * u j (w + x)) = fun j => u j w :=
      funext fun j => congrFun ((hu j).2 x hx h0) w
    rw [e]
    exact ht w

theorem lim_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := GlobalTheory.T.heisenbergBasisDeriv_eq_of_uniform_limits
theorem lim_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := GlobalTheory.T.theta_word_limits_smooth_along_real_points

theorem limit_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → F [] ∈ thetaLevel ψ S T U ∧ ∀ l, GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (F []) = F l := by
  intro D ψ hψ θ hθ S T U hU u hu F hF
  have h0 := lim_clauses D ψ S T U u hu (F []) (hF [])
  have hth : IsThetaFunO ψ S T (F []) :=
    ⟨h0.1, ⟨U, hU, h0.2.1⟩, h0.2.2, lim_smooth D ψ hψ θ hθ S T u (fun j => (hu j).1) F hF []⟩
  refine ⟨⟨hth, h0.2.1⟩, fun l => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact lim_deriv D ψ hψ θ hθ S T (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) (F (a :: l))
      (fun j => GlobalTheory.Size.theta_word hψ hθ l (hu j).1) (hF l) a (hF (a :: l))

theorem complete : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hC := GlobalTheory.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hlim : ∀ l w, ∃ z, Filter.Tendsto (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j) w) Filter.atTop (nhds z) :=
    fun l w => cauchySeq_tendsto_of_complete ((hC l).cauchySeq (Set.mem_univ w))
  choose F hF using hlim
  have hFu : ∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop :=
    fun l => tendstoUniformlyOn_univ.1 ((hC l).tendstoUniformlyOn_of_tendsto fun w _ => hF l w)
  obtain ⟨h1, h2⟩ := limit_theta D ψ hψ θ hθ S T U hU u hu F hFu
  refine ⟨F [], h1, GlobalTheory.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif D ψ hψ θ hθ S T μ 𝓕 hμ u (F []) h1.1 (fun j => (hu j).1) fun l => ?_⟩
  rw [h2 l]
  exact hFu l

end GlobalTheory.ThetaComplete
