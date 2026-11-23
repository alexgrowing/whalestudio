import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.ZcComm

variable {D : D7} {S T : HSp D}

def IsCarried (ψ : AddChar (AF D.host.F) ℂ) (om : WRep S T) (L : (GA D T → ℂ) → (GA D T → ℂ)) : Prop :=
  ∃ Δ : (WO S T → ℂ) → (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Δ f)) ∧
    (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Δ (f + f') = Δ f + Δ f') ∧
    (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Δ (c • f) = c • Δ f) ∧
    ∀ f, IsThetaFunO ψ S T f → ∀ g w, L (fun h => om (g, h) f w) = fun h => om (g, h) (Δ f) w

variable {ψ : AddChar (AF D.host.F) ℂ} (om : WRep S T)

theorem isCarried_id : IsCarried ψ om fun φ => φ :=
  ⟨fun f => f, fun _ hf => hf, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem isCarried_zero : IsCarried ψ om fun _ => 0 := by
  refine ⟨fun _ => 0, fun _ _ => (GlobalTheory.RealWeil.thetaSub ψ S T).zero_mem, fun _ _ _ _ => by simp,
    fun c _ _ => by simp, fun f _ g w => ?_⟩
  funext h
  simp

theorem isCarried_comp {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)} (h₁ : IsCarried ψ om L₁)
    (h₂ : IsCarried ψ om L₂) : IsCarried ψ om fun φ => L₁ (L₂ φ) := by
  obtain ⟨Δ₁, t₁, a₁, s₁, e₁⟩ := h₁
  obtain ⟨Δ₂, t₂, a₂, s₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ (Δ₂ f), fun f hf => t₁ _ (t₂ f hf), fun f f' hf hf' => ?_, fun c f hf => ?_,
    fun f hf g w => ?_⟩
  · beta_reduce
    rw [a₂ f f' hf hf', a₁ _ _ (t₂ f hf) (t₂ f' hf')]
  · beta_reduce
    rw [s₂ c f hf, s₁ c _ (t₂ f hf)]
  · beta_reduce
    rw [e₂ f hf g w, e₁ _ (t₂ f hf) g w]

theorem isCarried_add {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)} (h₁ : IsCarried ψ om L₁)
    (h₂ : IsCarried ψ om L₂) : IsCarried ψ om fun φ => L₁ φ + L₂ φ := by
  obtain ⟨Δ₁, t₁, a₁, s₁, e₁⟩ := h₁
  obtain ⟨Δ₂, t₂, a₂, s₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ f + Δ₂ f, fun f hf => (GlobalTheory.RealWeil.thetaSub ψ S T).add_mem (t₁ f hf) (t₂ f hf),
    fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g w => ?_⟩
  · beta_reduce
    rw [a₁ f f' hf hf', a₂ f f' hf hf']
    abel
  · beta_reduce
    rw [s₁ c f hf, s₂ c f hf, smul_add]
  · beta_reduce
    rw [e₁ f hf g w, e₂ f hf g w]
    funext h
    simp only [Pi.add_apply, map_add]

theorem isCarried_smul (c : ℂ) {L : (GA D T → ℂ) → (GA D T → ℂ)} (hL : IsCarried ψ om L) :
    IsCarried ψ om fun φ => c • L φ := by
  obtain ⟨Δ, t, a, s, e⟩ := hL
  refine ⟨fun f => c • Δ f, fun f hf => (GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c (t f hf),
    fun f f' hf hf' => ?_, fun c' f hf => ?_, fun f hf g w => ?_⟩
  · beta_reduce
    rw [a f f' hf hf', smul_add]
  · beta_reduce
    rw [s c' f hf, smul_comm c c']
  · beta_reduce
    rw [e f hf g w]
    funext h
    simp only [Pi.smul_apply, map_smul]

theorem isCarried_sum {ι : Type*} (s : Finset ι) (L : ι → (GA D T → ℂ) → (GA D T → ℂ))
    (hL : ∀ i ∈ s, IsCarried ψ om (L i)) : IsCarried ψ om fun φ => ∑ i ∈ s, L i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isCarried_zero (ψ := ψ) om
  | insert a s ha ih =>
    have := isCarried_add om (hL a (Finset.mem_insert_self a s))
      (ih fun i hi => hL i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using this

theorem isCarried_foldr {ι : Type*} (A : ι → (GA D T → ℂ) → (GA D T → ℂ)) (l : List ι)
    (hA : ∀ i ∈ l, IsCarried ψ om (A i)) : IsCarried ψ om fun φ => l.foldr (fun i g => A i g) φ := by
  induction l with
  | nil => simpa only [List.foldr_nil] using isCarried_id (ψ := ψ) om
  | cons i l ih =>
    have := isCarried_comp om (hA i (List.mem_cons.2 (Or.inl rfl)))
      (ih fun j hj => hA j (List.mem_cons.2 (Or.inr hj)))
    simpa only [List.foldr_cons] using this

theorem isCarried_gelf (θ : InfFam D) (τ : D.what₂.Tau)
    (hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z)) (k : ℕ) :
    IsCarried ψ om (Formalism.L2.Theta.gelf θ T τ k) := by
  refine isCarried_sum om Finset.univ _ fun idx _ => ?_
  refine isCarried_foldr om (fun L => L) _ fun L hL => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hL
  exact hR _

theorem isCarried_centreAct (θ : InfFam D) (τ : D.what₂.Tau)
    (hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z)) (z : MvPolynomial ℕ ℂ) :
    IsCarried ψ om (centreAct θ τ T z) := by
  refine isCarried_sum om z.support _ fun k _ => isCarried_smul om _ ?_
  exact isCarried_foldr om _ _ fun i _ => isCarried_gelf om θ τ hR i

end GlobalTheory.Core.Rk.ZcComm

open GlobalTheory.Core.Rk.ZcComm in

theorem GlobalTheory.Core.Rk.ZcComm.omCentreT_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (z : MvPolynomial ℕ ℂ), (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → omCentreT om θ τ z (f + f') = omCentreT om θ τ z f + omCentreT om θ τ z f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → omCentreT om θ τ z (c • f) = c • omCentreT om θ τ z f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g h, thetaKO om g h (omCentreT om θ τ z f) = centreAct θ τ T z (fun h' => thetaKO om g h' f) h := by
  intro D ψ θ S T χS χT om hθ hω τ z
  have hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z) := fun Z =>
    GlobalTheory.Core.Rk.ZcDer.rderC_om D ψ θ S T χS χT om hθ hω τ Z
  obtain ⟨Δ, -, ha, hs, he⟩ := isCarried_centreAct om θ τ hR z
  have key : ∀ f, IsThetaFunO ψ S T f → omCentreT om θ τ z f = Δ f := by
    intro f hf
    funext w
    show centreAct θ τ T z (fun h => om (1, h) f w) 1 = Δ f w
    rw [he f hf 1 w]
    show om (1, 1) (Δ f) w = Δ f w
    rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]
    rfl
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g h => ?_⟩
  · rw [key _ ((GlobalTheory.RealWeil.thetaSub ψ S T).add_mem hf hf'), key f hf, key f' hf', ha f f' hf hf']
  · rw [key _ ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf), key f hf, hs c f hf]
  · rw [key f hf]
    show om (g, h) (Δ f) 0 = centreAct θ τ T z (fun h' => om (g, h') f 0) h
    rw [he f hf g 0]
