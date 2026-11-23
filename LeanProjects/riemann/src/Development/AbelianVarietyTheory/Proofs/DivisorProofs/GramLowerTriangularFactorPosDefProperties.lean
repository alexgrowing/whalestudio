import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ}

theorem leadMinor_pos_of_posDef (h : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0 := by
  have h1 : 0 < leadMinor G j := (h.submatrix Subtype.val_injective).det_pos
  rw [Complex.lt_def] at h1
  exact ⟨by simpa using h1.1, by simpa using h1.2.symm⟩

theorem ldPart_diag_of_posDef (h : G.PosDef) (i : Fin s) : 0 < grD G i ∧ ldPart G i i = grD G i := by
  obtain ⟨a1, a2⟩ := leadMinor_pos_of_posDef h ((i : ℕ) + 1)
  obtain ⟨b1, b2⟩ := leadMinor_pos_of_posDef h (i : ℕ)
  refine ⟨div_pos a1 b1, ?_⟩
  have e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val := by
    funext a
    split_ifs with ha
    · exact ha.symm
    · rfl
  have ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using a2)
  have eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using b2)
  simp only [ldPart, Matrix.of_apply, grD]
  rw [e, Complex.ofReal_div, ← ea, ← eb]
  rfl

theorem ldPart_eq_zero_of_lt (G : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i < j) : ldPart G i j = 0 := by
  have hij' : (i : ℕ) < j := hij
  simp only [ldPart, Matrix.of_apply]
  rw [Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]
  · intro h
    exact hij.ne (congrArg Subtype.val h)
  · funext b
    simp [Matrix.submatrix_apply]

theorem ldPart_posDef_spec : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  intro s G h
  refine ⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩
  rw [Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)),
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ldPart_diag_of_posDef h i
  rw [h2]
  exact_mod_cast h1.ne'

end GlobalTheory.ChernCalc
