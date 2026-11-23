import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

def gconv (g g' : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t, g t * g' (r - t)

theorem gconv_comm (g g' : ℝ → ℝ) : gconv g g' = gconv g' g := by
  funext r
  unfold gconv
  rw [← integral_sub_left_eq_self (fun t => g t * g' (r - t)) volume r]
  simp [mul_comm]

variable {n : ℕ}

def KReg {V : Type} [NormedAddCommGroup V] (k : Mat n → V) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

theorem inv_mem_GLs {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  have : y.det ≠ 0 := hy
  change (y⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero this

section
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem isMult_of_fintype {ι : Type} [Fintype ι] {k : Mat n → (E.V →L[ℂ] E.V)} {val : Inf n → ℂ} {T : ℝ}
    (c : ι → ℂ) (w : ι → List (Bool × ℕ)) (g : ι → ℝ → ℝ) (ks : ι → Mat n → (E.V →L[ℂ] E.V))
    (h1 : ∀ i, IsBump (g i) T ∧ IsKer μ E (w i) (g i) (ks i)) (h2 : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y)
    (h3 : ∀ χ, val χ = ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)) : IsMult μ E k val T := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, c ∘ e.symm, w ∘ e.symm, g ∘ e.symm, ks ∘ e.symm, fun i => h1 _, fun y hy => ?_, fun χ => ?_⟩
  · rw [h2 y hy]
    exact (Equiv.sum_comp e.symm (fun i => c i • ks i y)).symm
  · rw [h3 χ]
    exact (Equiv.sum_comp e.symm (fun i => c i * zVal (w i) χ * coshT (g i) (cas χ))).symm
end

theorem zVal_append (w w' : List (Bool × ℕ)) (χ : Inf n) : zVal (w ++ w') χ = zVal w χ * zVal w' χ := by
  simp [zVal]

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

end Ops

section Alg

variable {A : Type} [Ring A]

noncomputable def Epw (e : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, e a c * Epw e m c b

def trE (e : Fin n → Fin n → A) (m : ℕ) : A := ∑ a, Epw e m a a

noncomputable def bco (N : A) (τ : ℕ → A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => N * bco N τ m 0 - τ m
  | m + 1, j + 1 => bco N τ m j + N * bco N τ m (j + 1)

noncomputable def phiSeq (N : A) (τ : ℕ → A) (m : ℕ) : A :=
  τ m - ∑ j : Fin m, bco N τ m j * phiSeq N τ j
termination_by m
decreasing_by exact j.isLt

end Alg

def gser (c : Fin n → ℂ) : PowerSeries ℂ := PowerSeries.mk (GlobalTheory.Dec.gelfVal c)

end GlobalTheory.CompanionTheory.WaveMult
