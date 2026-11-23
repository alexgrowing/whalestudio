import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
