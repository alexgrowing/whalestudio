import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftGen

open GlobalTheory.RealWeil

theorem deriv_eq_of_norm {B H : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : B →L[ℂ] H) {u v : ℝ → B} {A G A' : B} (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0)
    (hn : ∀ t : ℝ, ‖Φ (v t - v 0 - (t : ℂ) • A')‖ = ‖Φ (u t - u 0 - (t : ℂ) • A)‖) : Φ G = Φ A' := by
  have h1 : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h2 : HasDerivAt (fun t => Φ (v t)) (Φ G) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  refine h2.unique ?_
  rw [hasDerivAt_iff_isLittleO] at h1 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
  refine h1.congr_left fun t => ?_
  have := hn t
  rw [map_sub, map_sub, map_sub, map_sub, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul] at this
  simp only [sub_zero]
  exact this.symm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem deriv_om (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (p : GA D S × GA D T) {u v : ℝ → BB ψ S T} {A G : BB ψ S T}
    (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0) (hut : ∀ t, IsThetaFunO ψ S T (u t).1)
    (hA : IsThetaFunO ψ S T A.1) (e : ∀ t, ((v t).1 : WO S T → ℂ) = om p (u t).1) :
    (G.1 : WO S T → ℂ) = om p A.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  let A' : BB ψ S T := toB hψ _ (hW.om_pres p _ hA)
  have hA' : (A'.1 : WO S T → ℂ) = om p A.1 := coe_toB _ _ _
  have hk : ∀ a b : BB ψ S T, IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have key : toL2 _ _ (μ.restrict 𝓕) G = toL2 _ _ (μ.restrict 𝓕) A' := by
    refine deriv_eq_of_norm _ hu hv fun t => ?_
    have e1 : ((u t - u 0 - (t : ℂ) • A).1 : WO S T → ℂ) =
        ((u t).1 : WO S T → ℂ) - ((u 0).1 : WO S T → ℂ) - (t : ℂ) • (A.1 : WO S T → ℂ) := rfl
    have e2 : ((v t - v 0 - (t : ℂ) • A').1 : WO S T → ℂ) = om p (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1, map_sub, map_sub, map_smul, ← e, ← e, ← hA']
      rfl
    have h3 : IsThetaFunO ψ S T (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (hut t) (hut 0)) ((thetaSub ψ S T).smul_mem _ hA)
    exact hk _ _ h3 e2
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (G - A')
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((G - A').1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (G - A').1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  rw [← hA']
  exact sub_eq_zero.1 h5

theorem hasDerivAt_om : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  intro D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  refine ⟨lam, fun F hF p w => ?_⟩
  obtain ⟨u, hu, hud⟩ := hlam F hF
  have hA : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F).1 := by
    have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
    rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
    exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem lam hF)
  have : IsTopologicalGroup (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.2.2.2.1
  have : IsTopologicalGroup (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.2.2.2.1
  have hn : ∀ V : HSp D, (GinfC V).Normal := fun V => MonoidHom.normal_ker _
  obtain ⟨lam', hlam'⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc (fun t => p * γ t * p⁻¹)
    ((continuous_const.mul hγ).mul continuous_const) (fun s t => by rw [hadd]; group)
    (fun t => ⟨(hn S).conj_mem _ (hinf t).1 p.1, (hn T).conj_mem _ (hinf t).2 p.2⟩)
    (mM θ S T p * X * mM θ S T p⁻¹) (fun k l => by
      simp only [map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ => (hX i j).const_mul _).mul_const _)
  obtain ⟨v, hv, hvd⟩ := hlam' (toB hψ _ (hW.om_pres p _ hF)) (by rw [coe_toB]; exact hW.om_pres p _ hF)
  have e : ∀ t, ((v t).1 : WO S T → ℂ) = om (p * γ t) F.1 := fun t => by
    rw [hv, coe_toB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have key := deriv_om hψ hW p hud hvd (fun t => by rw [hu]; exact hW.om_pres _ _ hF) hA
    (fun t => by rw [e, hu, map_mul, Module.End.mul_apply])
  rw [← key]
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvd
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (congrFun (e t) w).symm

end GlobalTheory.Mem.LiftGen
