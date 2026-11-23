import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.LowerHarm

open MvPolynomial

theorem deg_pderiv_succ {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical
  rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega

theorem pderiv_of_deg_zero {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]

theorem fockT_lower {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = - ∑ j : Fin n, pderiv (τ, i, j) (pderiv (τ, l, j) P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((i : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((l : ℕ) < p τ) = true := decide_eq_true hl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem lower_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k + 2) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k := by
  rw [fockT_lower τ p i l hi hl, totalDegree_neg]
  exact totalDegree_finsetSum_le fun j _ => deg_pderiv_succ _ _ _ (deg_pderiv_succ _ _ (k + 1) h)

theorem lower_zero {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (h : P.totalDegree ≤ 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = 0 := by
  rw [fockT_lower τ p i l hi hl]
  simp [pderiv_of_deg_zero _ _ (deg_pderiv_succ _ _ 0 h)]

theorem lower_to_harmonic : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  intro D n m p W _ _ _ M hM hne
  classical
  have hex : ∃ d, ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w, (ψ w).totalDegree ≤ d := by
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (ψ (b j)).totalDegree, ψ, hψ, hψ0, fun w => ?_⟩
    rw [← b.sum_repr w, map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (ψ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨ψ, hψ, hψ0, hdeg⟩ := Nat.find_spec hex
  refine ⟨ψ, hψ, hψ0, fun w τ i l hi hl => ?_⟩
  by_contra hne'
  have hL := hM ψ hψ τ i l hi hl
  have hL0 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ≠ 0 := fun h => hne' (by simpa using LinearMap.congr_fun h w)
  rcases Nat.lt_or_ge (Nat.find hex) 2 with h2 | h2
  · exact hne' (lower_zero τ p i l hi hl _ (by have := hdeg w; omega))
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
    have := Nat.find_min' hex ⟨_, hL, hL0, fun w' => lower_deg τ p i l hi hl _ k (hk ▸ hdeg w')⟩
    omega

end GlobalTheory.LowerHarm
