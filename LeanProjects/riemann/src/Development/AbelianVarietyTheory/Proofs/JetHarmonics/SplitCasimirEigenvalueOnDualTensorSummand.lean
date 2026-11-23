import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem dualTens_casimir_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) (i : Fin n) :
    ∑ a, ∑ b, dualTens E a b (dualTens E b a x) i
      = Formalism.REAL.Cas E (x i) + (2 : ℂ) • splitCas E x i + (n : ℂ) • x i := by
  have h : ∀ a b, dualTens E a b (dualTens E b a x) i
      = E a b (E b a (x i)) - (if i = a then E a b (x b) else 0) - (if i = b then E b a (x a) else 0)
        + (if i = b then x b else 0) := by
    intro a b
    simp only [dualTens, map_sub, if_true]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  have h1 : ∑ a, ∑ b, (if i = a then E a b (x b) else 0) = ∑ c, E i c (x c) := by
    rw [Finset.sum_comm]; simp
  have h2 : ∑ a, ∑ b, (if i = b then E b a (x a) else 0) = ∑ c, E i c (x c) := by
    simp
  have h3 : ∑ _a : Fin n, ∑ b, (if i = b then x b else 0) = (n : ℂ) • x i := by
    simp [Nat.cast_smul_eq_nsmul]
  have h4 : ∑ a, ∑ b, E a b (E b a (x i)) = Formalism.REAL.Cas E (x i) := by
    simp [Formalism.REAL.Cas, LinearMap.sum_apply]
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4, splitCas, two_smul]
  abel

theorem casG_sub_single {n : ℕ} (mu : Fin n → ℝ) (s : Fin n) :
    casG (mu - Pi.single s 1) = casG mu - 2 * mu s + 1 := by
  have h : ∀ a, (mu - Pi.single s (1 : ℝ) : Fin n → ℝ) a ^ 2
      = mu a ^ 2 + (if a = s then - 2 * mu s + 1 else 0) := by
    intro a
    by_cases ha : a = s
    · subst ha; simp; ring
    · simp [ha]
  simp only [casG, h, Finset.sum_add_distrib]
  simp
  ring

theorem splitCas_on_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  intro M _ _ Ns _ _ n E F io mu s hE hF hio y
  funext i
  have h1 : io (Formalism.REAL.Cas F y) i = ∑ a, ∑ b, dualTens E a b (dualTens E b a (io y)) i := by
    simp [Formalism.REAL.Cas, LinearMap.sum_apply, map_sum, Finset.sum_apply, hio]
  rw [dualTens_casimir_apply, hE, hF, map_smul, casG_sub_single, Pi.smul_apply] at h1
  have h2 : (2 : ℂ) • splitCas E (io y) i
      = (2 : ℂ) • (((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y i) := by
    have h3 : (2 : ℂ) • splitCas E (io y) i
        = ((casG mu - 2 * mu s + 1 : ℝ) : ℂ) • io y i - (casG mu : ℂ) • io y i - (n : ℂ) • io y i := by
      rw [h1]; abel
    rw [h3, ← sub_smul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [Pi.smul_apply]
  exact smul_right_injective M (two_ne_zero) h2

end GlobalTheory
