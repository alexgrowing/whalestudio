import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThK.DiagDeriv

theorem prod_ofFn_ite {M : Type*} [Monoid M] : ∀ {k : ℕ} (i : Fin k) (x : M),
    (List.ofFn fun j => if j = i then x else 1).prod = x
  | 0, i, _ => i.elim0
  | k + 1, i, x => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [Fin.succ_ne_zero]
    · have := prod_ofFn_ite i' x
      simp only [Fin.succ_inj, (Fin.succ_ne_zero i').symm, if_false, one_mul]
      exact this

theorem hasDerivAt_prod_ofFn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (k : ℕ) (δ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (δ i)) →
    ∀ f : GAd σ J → ℂ, IsSm σ J f → ∀ g,
      HasDerivAt (fun t : ℝ => f (g * (List.ofFn fun i => δ i t).prod)) (∑ i, lineDer (δ i) f g) 0 := by
  intro F E _ _ _ _ _ σ hCM n J k δ hδ f hf g
  set Φ : (Fin k → ℝ) → ℂ := fun t => f (g * (List.ofFn fun i => δ i (t i)).prod) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hf k δ hδ g
  have hd : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h1 : ∀ j, δ j 0 = 1 := fun j => by
    have e := isRealLine_add F E σ hCM n J (δ j) (hδ j) 0 0
    rw [add_zero] at e
    exact (mul_left_cancel (a := δ j 0) (e.symm.trans (mul_one _).symm))
  have hsingle : ∀ i, (fun s : ℝ => f (g * δ i s)) = fun s => Φ (Pi.single i s) := fun i => funext fun s => by
    simp only [hΦdef]
    congr 2
    rw [← prod_ofFn_ite (M := GAd σ J) i (δ i s)]
    congr 1
    refine List.ofFn_inj.2 (funext fun j => ?_)
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h, h1]
  have hpart : ∀ i, fderiv ℝ Φ 0 (Pi.single i 1) = lineDer (δ i) f g := fun i => by
    have hs : HasDerivAt (fun s : ℝ => (Pi.single i s : Fin k → ℝ)) (Pi.single i 1) 0 := by
      refine hasDerivAt_pi.2 fun j => ?_
      by_cases h : j = i
      · subst h; simpa using hasDerivAt_id' (0 : ℝ)
      · simpa [Pi.single_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    have := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hd hs (by simp)
    simp only [lineDer]
    rw [hsingle i]
    exact this.deriv.symm
  have hc : HasDerivAt (fun t : ℝ => (fun _ : Fin k => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hd hc rfl
  refine this.congr_deriv ?_
  rw [show (fun _ : Fin k => (1 : ℝ)) = ∑ i, Pi.single i 1 from (Finset.univ_sum_single _).symm, map_sum]
  exact Finset.sum_congr rfl fun i _ => hpart i

end GlobalTheory.ThK.DiagDeriv

end
