import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftFockVec

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem ptAt_isFockVec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h'
  obtain ⟨⟨hψ, hv⟩, -⟩ := hlv
  have hθ : IsInfFam R.θ := hv.inf
  obtain ⟨⟨p, hp⟩, -⟩ := hv.norm
  obtain ⟨-, hθf, hS, hvac⟩ := GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h p.1 p.2 hp
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ)
  set Ap := aPlusAll (heisO R.ψ (Vc D i) (Wc D i)) R.θ (fun τ => cplxO ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) (cart (R.MW i σ) τ)) (R.BV i) BW with hAdef
  have hadd : ∀ g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (g + g') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (a • g) :=
    fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (Ap k g) :=
    fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i' j g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (Ap j g) = Ap j (Ap i' g) :=
    fun i' j _ h => aPlus_comm' hψ hθ i'.1 _ hS hT j.1 _ h
  have Aadd : ∀ i' g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      Ap i' (g + g') = Ap i' g + Ap i' g' :=
    fun i' _ _ h h' => aPlus_add hψ hθ i'.1 _ _ h h'
  have Asm : ∀ i' (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (a • g) = a • Ap i' g :=
    fun i' a _ h => aPlus_smul hψ hθ i'.1 _ _ a h
  have hpt' : ∀ Q', ptAt R i σ BW f Q' = pureTensorL Ap f Q' := fun _ => rfl
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ c' : FVar D (Wc D i).rank (Vc D i).rank → ℂ, ∀ Q',
      annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) z (pureTensorL Ap f Q') =
        pureTensorL Ap f (∑ k, c' k • MvPolynomial.pderiv k Q') := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir (Vc D i) (Wc D i) τ z k.1 (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir (Vc D i) (Wc D i) τ (cplxO 1 (cart (R.MW i σ) τ) z) k.1
          (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ))), fun Q' => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hθf (hvac τ z) Q'
  refine ⟨hpt Q, Q.totalDegree + 1, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ Q' : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ,
      l.foldr (fun p g => annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ p.1 (cplxO 1 (cart (R.MW i σ) p.1)) p.2 g)
          (pureTensorL Ap f Q) = pureTensorL Ap f Q' ∧
        ∀ n : FVar D (Wc D i).rank (Vc D i).rank →₀ ℕ, Q.totalDegree < n.degree + l.length → Q'.coeff n = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨Q, rfl, fun n hn => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h2 : Q.totalDegree < n.degree := by simpa using hn
      exact h2
    | cons q l ih =>
      obtain ⟨Q', hQ', hQc⟩ := ih
      obtain ⟨c', hc'⟩ := hder q.1 q.2
      refine ⟨∑ k, c' k • MvPolynomial.pderiv k Q', ?_, fun n hn => ?_⟩
      · rw [List.foldr_cons, hQ', hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c' Q' (Q.totalDegree - l.length)
          (fun n' hn' => hQc n' (by omega)) n ?_
        simp only [List.length_cons] at hn
        omega
  obtain ⟨Q', hQ', hQc⟩ := key l
  have hQ0 : Q' = 0 := MvPolynomial.ext _ _ fun n => by
    rw [hQc n (by rw [hl]; omega), MvPolynomial.coeff_zero]
  show l.foldr _ (ptAt R i σ BW f Q) = 0
  rw [hpt', hQ', hQ0, map_zero]

end GlobalTheory.LiftFockVec

end
