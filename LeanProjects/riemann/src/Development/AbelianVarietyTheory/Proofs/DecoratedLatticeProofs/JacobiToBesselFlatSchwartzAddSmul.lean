import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatAdd

variable {D : D7}

theorem mixS_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (f + g) x = d.mixS T ψ μ 𝓕 f x + d.mixS T ψ μ 𝓕 g x := by
  funext w₀
  have h1 := d.integrableOn_mixS hψ hμ hf x w₀
  have h2 := d.integrableOn_mixS hψ hμ hg x w₀
  simp only [HypDec.integrandS_eq] at h1 h2
  simp only [HypDec.mixS, Pi.add_apply, HypDec.integrandS_eq]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem continuous_mixS {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) : Continuous (d.mixS T ψ μ 𝓕 f x) := by
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have c0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
  refine GlobalTheory.MixCont.continuous_covolOne_integral hμ
    (fun (w : WO S₀ T) a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) ?_
    (fun w γ hγ a => d.integrandS_periodic hf x w γ hγ a)
  have e : Function.uncurry (fun (w : WO S₀ T) a =>
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) =
      fun z => ψ (symplOH S T (d.extY T z.2) (d.extX T x)) * f (d.extY T z.2 + d.extX T x + d.ext0 T z.1) := by
    funext z; exact d.integrandS_eq _ _ _ _
  rw [e]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cY.comp continuous_snd) continuous_const)).mul
    (hf.cont.comp (((cY.comp continuous_snd).add continuous_const).add (c0.comp continuous_fst)))

theorem integrableOn_mixT_of_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (S : HSp D) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hc : Continuous f)
    (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    IntegrableOn
      (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (GlobalTheory.MixCont.integrandT_periodic_of_quasi d hq y w₀)
  have cX : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  simp only [HypDec.integrandT_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH cX continuous_const)).mul
    (hc.comp ((cX.add continuous_const).add continuous_const))

theorem evalAt_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) :
    evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (f + g) x y =
      evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 f x y + evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 g x y := by
  funext w₀
  have h1 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hf x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hf x δ w) y w₀
  have h2 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hg x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hg x δ w) y w₀
  simp only [HypDec.integrandT_eq] at h1 h2
  simp only [evalAt, mixS_add hψ dV W vS.covol hf hg x, HypDec.mixT, Pi.add_apply, HypDec.integrandT_eq]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem flatFB_add_smul : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (f g : WO J.W B.V → ℂ),
    IsThetaFunO ψ J.W B.V f → IsThetaFunO ψ J.W B.V g →
    flatFB st (f + g) = flatFB st f + flatFB st g ∧ ∀ a : ℂ, flatFB st (a • f) = a • flatFB st f := by
  intro D hF ψ hψ σ J B st f g hf hg
  refine ⟨?_, fun a => GlobalTheory.HandHom.flatFB_smul st a f⟩
  have hif := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 f hf).1
  have hig := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 g hg).1
  rw [GlobalTheory.Unf.FlatTheta.rat_lastQ] at hif hig
  funext w
  simp only [flatFB, flatLast, flatAt, Pi.add_apply]
  rw [← integral_add (hif w) (hig w)]
  congr 1; funext u
  simp only [flatFun, evalAt_add hψ.1.1 J.d B.d st.vS st.vT hf hg, Pi.add_apply, mul_add]

end GlobalTheory.FlatAdd

end
