import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.OrientedHeis

theorem l2O_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    l2O μ 𝓕 (heisO ψ S T u g) = l2O μ 𝓕 g := by
  have hg' := GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg u
  have e := ipO_heisO hψ hμ.1 hμ.2.1 hg hg u
  rw [ipO_self, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg'.cont, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg.cont, Complex.ofReal_inj,
    pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero] at e
  exact (ENNReal.toReal_eq_toReal_iff' (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg') (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg)).1 e

theorem sobO_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {h : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) {u : WO S T}
    (hu : u.map (infPart D) = 0) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (heisO ψ S T u h) = sobO ψ θ μ 𝓕 d h := by
  have := wordSum_eq_mul (A := heisDer ψ θ) (p := l2O μ 𝓕) (d := d) (x := h) (y := heisO ψ S T u h) (c := 1)
    fun l => by
      have e : wordAct (heisDer ψ θ) l (heisO ψ S T u h) = heisO ψ S T u (wordAct (heisDer ψ θ) l h) :=
        wordAct_rel (R := fun g g' => g = heisO ψ S T u g') l
          (fun a _ _ _ e => e ▸ GlobalTheory.FinTranslate.dRho_heisO hθ hu a.1 _ _) rfl
      rw [e, one_mul, l2O_heisO_eq hψ hθ hμ (theta_word hψ hθ l hh) u]
  rw [one_mul] at this
  exact this

end GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.HeisTranslateBound GlobalTheory.OrientedHeis in

theorem GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h → ∀ d : ℕ, GlobalTheory.Size.sobO ψ θ μ 𝓕 d (c.sum fun u z => z • heisO ψ S T u h) ≤ (∑ u ∈ c.support, ‖c u‖ₑ) * GlobalTheory.Size.sobO ψ θ μ 𝓕 d h := by
  intro D ψ θ S T hψ hθ μ 𝓕 hμ c hc h hh d
  have ht : ∀ u, IsThetaFunO ψ S T (c u • heisO ψ S T u h) := fun u =>
    theta_smul (c u) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hh u)
  refine (sobO_sum_le hψ hθ c.support (g := fun u => c u • heisO ψ S T u h) (fun u _ => ht u) d).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [sobO_smul, sobO_heisO_eq hψ hθ hμ hh (hc u hu)]
