import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareComm.LineDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

private theorem hD_eq_mul_add_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (w : G)
    (hf : DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0) (u : R) :
    hD ι π om u f w =
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hlin : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hF : HasDerivAt (fun t : ℝ => f (w + ι (t • u))) (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have h0 : ((0 : ℝ) • u) = 0 := zero_smul ℝ u
    have hf' : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) := by rwa [h0]
    have := hf'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlin
    rw [h0] at this
    exact this
  have hP : HasDerivAt (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ)))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))) =
        fun t : ℝ => Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) := by
      funext t
      rw [map_smul, smul_eq_mul]
      push_cast
      ring_nf
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)))
        (1 * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const _
    simpa using h1.cexp
  have hPF := hP.mul hF
  unfold hD
  exact hPF.deriv.trans (by simp)

theorem dLine_eq_sum_dRho {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  classical
  obtain ⟨σ, hσ⟩ := exists_chart hθ
  funext w
  have hd : DifferentiableAt ℝ (fun x => f (w + iotaW σ T S x)) 0 :=
    ((theta_sm hσ hf w).differentiable (by simp)).differentiableAt
  rw [Finset.sum_apply, dLine_eq_hD hσ hψ hL f, hD_eq_mul_add_fderiv _ _ _ _ _ hd]
  have hτ : ∀ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f w =
      (-(Real.pi * Complex.I) * ((omO S T (piW θ T S w) (Pi.single τ (compAt θ τ (L 1))) : ℝ) : ℂ)) * f w +
        fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (Pi.single τ (compAt θ τ (L 1))) := by
    intro τ
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ _) f, GlobalTheory.FockIndep.piW_lineAt hθ τ]
    exact hD_eq_mul_add_fderiv _ _ _ _ _ hd _
  rw [Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_add_distrib]
  have hp : piW θ T S (L 1) = ∑ τ, (Pi.single τ (compAt θ τ (L 1)) : RW T S) := by
    exact (Finset.univ_sum_single (piW θ T S (L 1))).symm
  rw [hp, map_sum, map_sum]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

theorem deriv_line_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X), ∀ Φ ∈ algF ψ θ ε A B,
      ∀ L : ℝ →+ WO (sgn ε M) X, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
        (fun x => deriv (fun t : ℝ => heisO ψ (sgn ε M) X (L t) Φ x) 0) ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε M X A B Φ hΦ L hLc hLf
  have hsub : algF ψ θ ε A B ≤ GlobalTheory.RealWeil.thetaSub ψ (sgn ε M) X := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, P, hg, rfl⟩
    have hg' : IsThetaFunO ψ (sgn ε M) X g := hg.1
    show IsThetaFunO ψ (sgn ε M) X (fockF ψ θ ε A B g P)
    unfold fockF pureTensorO aPlusAll
    exact GlobalTheory.FockIndep.pure_mem (fun _ _ h h' => GlobalTheory.OrientedHeis.theta_add h h')
      (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
      (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) hg' P
  have hth : IsThetaFunO ψ (sgn ε M) X Φ := hsub hΦ
  have hL : IsRealDir X (sgn ε M) L := ⟨hLc, hLf⟩
  show dLine ψ (sgn ε M) X L Φ ∈ algF ψ θ ε A B
  rw [dLine_eq_sum_dRho hψ hθ hL hth]
  exact Submodule.sum_mem _ fun τ _ => GlobalTheory.SquareComm.dRho_mem_algF D ψ θ hψ hθ ε M X A B Φ hΦ τ _

end GlobalTheory.SquareComm.LineDeriv

end
