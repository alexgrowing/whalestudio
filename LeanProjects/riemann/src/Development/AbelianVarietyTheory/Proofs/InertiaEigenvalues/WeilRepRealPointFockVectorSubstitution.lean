import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.RealFockVac

theorem om_stdF_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∀ a ∈ GinfC V, ∀ u : GlobalTheory.ExportSeries.GLR D V.rank,
    (∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)) →
    ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
    ∀ P : MvPolynomial (FVar D W.rank V.rank) ℂ,
      om (a, 1) (stdF ψ θ V W sW BW f P) =
        stdF ψ θ V W sW BW (om (a, 1) f) (GlobalTheory.ExportSeries.fockSubst (fun _ => p) u P) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hBW a ha u hu f hf _ P
  obtain ⟨hPr, -, -, -, -, -, -, hT, -⟩ := hP
  have hom := hPr.weil
  have hθ : IsInfFam θ := hPr.inf
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one _ _
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := GlobalTheory.SmoothVac.isCartanInv_one V hPr.std
  have hG : ∀ τ, gramAt D V τ = 1 := fun τ => by
    rw [gramAt, hPr.std, Matrix.map_one _ (map_zero _) (map_one _)]
  have hun : ∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈
      Matrix.unitaryGroup (Fin V.rank) ℂ := fun τ => by
    rw [hu τ]
    have h1 : (compAt θ τ (Formalism.L2.Theta.mt V a))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V a) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    rw [hG, Matrix.mul_one] at h1
    exact Matrix.mem_unitaryGroup_iff'.2 h1
  have ht : ∀ τ, sW τ * BW τ = BW τ * diagonal fun b : Fin W.rank =>
      if decide (b.val < (fun _ => p) τ) = true then (1 : ℂ) else -1 := fun τ => by
    obtain ⟨ε, hε, -, h2⟩ := hBW τ
    have e : (fun b => (ε b : ℂ)) = fun b : Fin W.rank => if decide (b.val < p) = true then (1 : ℂ) else -1 :=
      funext fun b => by
        rcases hε b with h | h
        · simp [h.1, h.2]
        · simp [h.1, not_lt.2 h.2]
    rw [e] at h2
    exact h2
  have hBT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt W 1) * BW τ) = BW := funext fun τ => by rw [one, Matrix.one_mul]
  show om (a, 1) (pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f P) =
    pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW (om (a, 1) f) (GlobalTheory.ExportSeries.fockSubst (fun _ => p) u P)
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun τ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) * ((u τ : GL (Fin V.rank) ℂ) : Matrix _ _ ℂ)) sW sW BW
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W 1) * BW τ) a 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hu τ, Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) f hf P).2, hBT]
  exact GlobalTheory.RealFockAction.pureTensorO_subst hom.std hθ hS hT ht (fun _ => 1) u hun (hom.om_pres _ _ hf) P

end GlobalTheory.RealFockVac
