import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth

theorem contDiffOn_finsetProd {e : ℕ} {Un : Set (Fin e → ℂ)} {ι : Type} (s : Finset ι)
    (f : ι → (Fin e → ℂ) → ℂ)
    (h : ∀ i ∈ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ∏ i ∈ s, f i w) Un := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Fin e → ℂ => (1 : ℂ)) Un)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_det {e : ℕ} {Un : Set (Fin e → ℂ)} {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : (Fin e → ℂ) → Matrix σ σ ℂ)
    (h : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => m w a b) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (m w).det) Un := by
  have hdet : (fun w => (m w).det) =
      fun w => ∑ τ : Equiv.Perm σ, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, m w (τ i) i := by
    funext w
    exact Matrix.det_apply' _
  rw [hdet]
  exact ContDiffOn.sum fun τ _ => contDiffOn_const.mul
    (contDiffOn_finsetProd Finset.univ (fun i w => m w (τ i) i) fun i _ => h _ _)

theorem contDiffOn_minorIJ (N e : ℕ) (Un : Set (Fin e → ℂ))
    (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (h : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => minorIJ (A w) I J) Un := by
  by_cases hc : I.card = J.card
  · have hm : (fun w => minorIJ (A w) I J) =
        fun w => ((A w).submatrix (I.orderEmbOfFin hc) (J.orderEmbOfFin rfl)).det := by
      funext w
      rw [minorIJ, dif_pos hc]
    rw [hm]
    exact contDiffOn_det _ fun a b => h _ _
  · have hm : (fun w => minorIJ (A w) I J) = fun _ => (0 : ℂ) := by
      funext w
      rw [minorIJ, dif_neg hc]
    rw [hm]
    exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth
