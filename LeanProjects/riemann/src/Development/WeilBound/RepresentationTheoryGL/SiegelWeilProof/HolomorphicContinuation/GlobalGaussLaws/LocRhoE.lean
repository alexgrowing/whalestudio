import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Classical in

def substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    PX m n :=
  aeval (fun v : D.what₂.Tau × Fin m × Fin n × Bool => if v.1 = τ then
      (if v.2.2.2 then ∑ c, C (star (fr v.2.1 c)) * X (c, v.2.2.1, true) else ∑ c, C (fr v.2.1 c) * X (c, v.2.2.1, false))
    else 0) p

theorem evX_substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (u : Matrix (Fin m) (Fin n) ℂ) :
    evX (substP τ fr p) u = evalPoly p (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) := by
  classical
  unfold evX substP evalPoly
  rw [eval_aeval_subst]
  refine congrArg (fun x => MvPolynomial.eval x p) (funext fun v => ?_)
  obtain ⟨τ', a, j, b⟩ := v
  by_cases hτ : τ' = τ
  · subst hτ
    rw [if_pos rfl, dirAt_self]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]
    · simp only [↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, map_sum, Complex.star_def]
  · rw [if_neg hτ, dirAt_ne hτ]
    cases b <;> simp

theorem slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) :
    ∀ F ∈ fockA θ V n l s, ∃ Q : PX V.rank n, ∀ u : Matrix (Fin V.rank) (Fin n) ℂ,
      F (xL θ τ (fr * u)) = evX Q u * gs (cLoc l τ) u := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, g, -, rfl⟩ := hF
    refine ⟨C (g 0) * substP τ fr p, fun u => ?_⟩
    show evalPoly p (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * gauss V l s (fun τ' => compAt θ τ' (xL θ τ (fr * u))) *
        g (fun i j => finPart D ((xL θ τ (fr * u)) i j)) = _
    rw [compAt_xL hθ, finPart_xL hθ, gauss_dirAt hfr, ← evX_substP]
    simp only [evX, map_mul, eval_C]
    ring
  | zero => exact ⟨0, fun u => by simp [evX]⟩
  | add F G _ _ hF hG =>
    obtain ⟨Q₁, h₁⟩ := hF
    obtain ⟨Q₂, h₂⟩ := hG
    refine ⟨Q₁ + Q₂, fun u => ?_⟩
    simp only [Pi.add_apply, h₁, h₂, evX, map_add]
    ring
  | smul a F _ hF =>
    obtain ⟨Q, h⟩ := hF
    refine ⟨C a * Q, fun u => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, h, evX, map_mul, eval_C]
    ring

theorem tens_slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) (f : (Fin V.rank → Fin n → ℂ) → ℂ)
    (hf : tens θ τ fr f (psi0 θ V n l s τ) ∈ fockA θ V n l s) : ∃ Q : PX V.rank n, f = fP (cLoc l τ) Q := by
  obtain ⟨Q, hQ⟩ := slice hθ hfr l _ hf
  refine ⟨Q, funext fun (u : Matrix (Fin V.rank) (Fin n) ℂ) => ?_⟩
  have h := hQ u
  have hinv : fr⁻¹ * (fr * u) = u := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
  have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
    have := congrFun (compAt_xL hθ τ (fr * u)) τ
    simpa [dirAt_self] using this
  have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
    unfold psi0
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
    simp only [one_mul]
    exact gaussian_at_zero_eq_one D V.rank n
  simp only [tens] at h
  rw [hc, hinv, hp, mul_one] at h
  exact h

end PositivityTheory.Rg.Sw.Glob.RhoH
