import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareComm.AlgDeriv

open Complex GlobalTheory.FockIndep GlobalTheory.ArchRec.DerFock
open scoped Real

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem exists_dRho_pure_all (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS frS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (εS : D.what₂.Tau → Fin S.rank → Bool)
    (sT frT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (εT : D.what₂.Tau → Fin T.rank → Bool)
    (hfS : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D S ρ) (sS ρ) (εS ρ) (frS ρ))
    (hfT : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D T ρ) (sT ρ) (εT ρ) (frT ρ))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ L : Module.End ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ), ∀ f, IsThetaFunO ψ S T f →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → ∀ P,
      Datum.dRho (heisO ψ S T) θ τ z (pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f P) =
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f (L P) := by
  classical
  have hS := fun ρ => isCartanInv_of_isFrameOf (hfS ρ)
  have hT := fun ρ => isCartanInv_of_isFrameOf (hfT ρ)
  let A : FVar D T.rank S.rank → (WO S T → ℂ) → (WO S T → ℂ) :=
    aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ)) (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)
  let u : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun k => unitMap (frS τ)⁻¹ (frT τ)⁻¹ k.1 k.2
  let α : Fin T.rank × Fin S.rank → ℂ := fun k =>
    if (εT τ k.1 == εS τ k.2) then (frT τ * z * (frS τ)⁻¹) k.1 k.2
    else starRingEnd ℂ ((frT τ * z * (frS τ)⁻¹) k.1 k.2)
  let c : FVar D T.rank S.rank → ℂ := fun k => if k.1 = τ then (fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) *
    ((omDir S T τ z τ (u k.2) : ℝ) + I * (omDir S T τ (cplxO (sS τ) (sT τ) z) τ (u k.2) : ℝ))) else 0
  refine ⟨(1 / 2 : ℂ) • ((∑ k, c k • (MvPolynomial.pderiv k).toLinearMap) +
    (fockScale D τ : ℂ) • ∑ k : Fin T.rank × Fin S.rank,
      α k • LinearMap.mulLeft ℂ (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank))), fun f hf hv P => ?_⟩
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A k g) := fun k _ h => aPlus_theta hψ hθ k.1 _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g) := by
    rintro ⟨ρ, a, b⟩ ⟨ρ', a', b'⟩ g h
    by_cases e : ρ = ρ'
    · subst e
      exact aPlus_comm (hS ρ) (hT ρ) _ _ hψ hθ h
    · exact GlobalTheory.TwoPlaceComm.aPlus_comm_ne hψ hθ e _ _ _ _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hm := pure_mem hadd hsm hA hf P
  have hBA : ∀ j g, IsThetaFunO ψ S T g → Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (A j g) =
      A j (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) + c j • g := by
    rintro ⟨ρ, a, b⟩ g h
    by_cases e : ρ = τ
    · subst e
      refine (annih_aPlus (hS ρ) (hT ρ) z (u (a, b)) hψ hθ h).trans ?_
      congr 2
      exact (if_pos rfl).symm
    · rw [show c (ρ, a, b) = 0 from if_neg e, zero_smul, add_zero]
      exact GlobalTheory.TwoPlaceComm.annih_aPlus_ne hψ hθ (Ne.symm e) _ _ _ _ h
  have h1 := pure_deriv (B := Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z) (c := c) hadd hsm hA hc Aadd Asm
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h) hBA hf (hv z) P
  have h2 : Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (pureTensorL A f P) =
      pureTensorL A f (∑ k : Fin T.rank × Fin S.rank,
        α k • (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank) * P)) := by
    conv_lhs => rw [eq_sum_unitMap (hfS τ).1 (hfT τ).1 z]
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hm _ _ (cplxO_unitMap (hfS τ) (hfT τ) k.1 k.2), map_smul,
      pure_X_mul hadd hsm hA hc Aadd Asm hf]
    rfl
  have h3 : ∀ g, Datum.dRho (heisO ψ S T) θ τ z g =
      (1 / 2 : ℂ) • (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g +
        (fockScale D τ : ℂ) • Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) := fun g => by
    rw [Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero τ), one_smul, Datum.annih, Datum.crea]
    module
  change Datum.dRho (heisO ψ S T) θ τ z (pureTensorL A f P) = pureTensorL A f _
  rw [h3, h1, h2, ← map_smul, ← map_add, ← map_smul]
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
  rfl

end GlobalTheory.SquareComm.AlgDeriv

open GlobalTheory.SquareComm.AlgDeriv in

theorem GlobalTheory.SquareComm.dRho_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε S X A B f hf τ z
  have hth : ∀ g ∈ algF ψ θ ε A B, IsThetaFunO ψ (sgn ε S) X g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, P, hf₀, rfl⟩ := hx
      exact GlobalTheory.FockIndep.pure_mem (A := aPlusAll (heisO ψ (sgn ε S) X) θ
          (fun ρ => cplxO ((frSgn ε A).cart ρ) (B.cart ρ)) A.onb B.onb) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun k _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 _ _ h) hf₀.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul a x _ hx => exact GlobalTheory.OrientedHeis.theta_smul a hx
  obtain ⟨L, hL⟩ := exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart (frSgn ε A).fr (frSgn ε A).ε
    B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
    (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ z
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hf₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨f₀, L P, hf₀, hL f₀ hf₀.1 (hf₀.2 τ) P⟩
  | zero =>
    have h0 := GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε S) (T := X))
    rw [zero_smul, zero_smul] at h0
    rw [h0]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [GlobalTheory.FockIndep.dRho_add (S := sgn ε S) (T := X) hψ hθ τ z (hth x hx) (hth y hy)]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z a (hth x hx)]
    exact Submodule.smul_mem _ a ih

end
