import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockVecOfVac

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem coeff_sum_pderiv_eq_zero {ι : Type} [Fintype ι] (c : ι → ℂ) (Q : MvPolynomial ι ℂ) (n : ℕ)
    (hQ : ∀ m : ι →₀ ℕ, n < m.degree → Q.coeff m = 0) (m : ι →₀ ℕ) (hm : n < m.degree + 1) :
    (∑ i, c i • MvPolynomial.pderiv i Q).coeff m = 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_pderiv,
    hQ _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul, smul_zero]

theorem fock_of_vac : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  intro D V W S S' M M' θ ψ hψ hθ f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) (cart M τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M
  have hT : ∀ τ, IsCartanInv (gramAt D W τ) (cart M' τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M'
  set A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) := fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (A k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ V W g → A i (A j g) = A j (A i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ V W g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptOf ψ θ M M' f Q = pureTensorL A f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ V W (pureTensorL A f Q) := pure_mem hadd hsm hA hf.theta

  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ c : FVar D W.rank V.rank → ℂ, ∀ Q,
      annih (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) z (pureTensorL A f Q) =
        pureTensorL A f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir V W τ z k.1 (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir V W τ (cplxO (cart M τ) (cart M' τ) z) k.1
          (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.theta (hf.vac τ z) Q
  refine ⟨by rw [hpt]; exact hm P, P.totalDegree + 1, fun l hl => ?_⟩

  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Q : MvPolynomial (FVar D W.rank V.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ V W) θ p.1 (cplxO (cart M p.1) (cart M' p.1)) p.2 g) (pureTensorL A f P) =
        pureTensorL A f Q ∧ ∀ m : FVar D W.rank V.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length) (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    rw [hQc m (by rw [hl]; omega), MvPolynomial.coeff_zero]
  rw [hpt, hQ, hQ0, map_zero]

end GlobalTheory.FockVecOfVac

end
