import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootIdx
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
open GlobalTheory.BcEigen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcEigen

def rootEquiv (ι : Type) (N j : ℕ) (h : j ≤ N) : ι × Fin N ≃ Σ a : ι × Bool, Fin (rkB ι N j a) where
  toFun := rootIdx ι N j
  invFun z := match z with
    | ⟨(τ, true), i⟩ => (τ, ⟨i, by have := i.isLt; simp [rkB] at this; omega⟩)
    | ⟨(τ, false), i⟩ => (τ, ⟨j + i, by have := i.isLt; simp [rkB] at this; omega⟩)
  left_inv x := by
    obtain ⟨τ, i⟩ := x
    by_cases hi : (i : ℕ) < j
    · simp [rootIdx, hi]
    · simp only [rootIdx, hi, dite_false]
      ext <;> simp; omega
  right_inv z := by
    obtain ⟨⟨τ, b⟩, i⟩ := z
    cases b
    · have hi : ¬ (j + (i : ℕ) < j) := by omega
      simp only [rootIdx, hi, dite_false]
      congr 1
      simp
    · have hi : (i : ℕ) < j := by have := i.isLt; simp [rkB] at this; omega
      simp [rootIdx, hi]

lemma rootEquiv_apply (ι : Type) (N j : ℕ) (h : j ≤ N) (x : ι × Fin N) :
    rootEquiv ι N j h x = rootIdx ι N j x := rfl

lemma rootIdx_fst_snd (ι : Type) (N j : ℕ) (x : ι × Fin N) :
    (rootIdx ι N j x).1.2 = decide ((x.2 : ℕ) < j) := by
  unfold rootIdx; split_ifs with hx <;> simp [hx]

end GlobalTheory.BcEigen

namespace GlobalTheory.BcEigen
open GlobalTheory.FlagPoly

lemma rename_rootIdx_lin (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (h : j ≤ N) (f : Bool → ℝ) :
    rename (rootIdx ι N j) (∑ τ, ∑ i : Fin N, C (f (decide ((i : ℕ) < j))) * X (τ, i) : Pol ι N) =
      ∑ a, C (f a.2) * eSum (rkB ι N j) a := by
  have hR : (∑ a, C (f a.2) * eSum (rkB ι N j) a : MvPolynomial (Σ a : ι × Bool, Fin (rkB ι N j a)) ℝ) =
      ∑ z : Σ a : ι × Bool, Fin (rkB ι N j a), C (f z.1.2) * X z := by
    rw [Fintype.sum_sigma]
    simp only [eSum, Finset.mul_sum]
  rw [hR, ← Equiv.sum_comp (rootEquiv ι N j h), Fintype.sum_prod_type]
  simp only [map_sum, map_mul, rename_C, rename_X, rootEquiv_apply, rootIdx_fst_snd]

theorem relabel_sums : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), j ≤ N →
    rename (rootIdx ι N j) (∑ τ, pSum τ 2 : Pol ι N) = sq2 (rkB ι N j) ∧
    rename (rootIdx ι N j) (lamA ι N j) = linE (rkB ι N j) lamSign ∧
    ∀ al be : ℝ, rename (rootIdx ι N j) (invForm j (fun _ : ι => al) (fun _ => be) : Pol ι N) =
      ∑ a, C (cond a.2 al be) * eSum (rkB ι N j) a := by
  intro ι _ _ N j h
  refine ⟨?_, ?_, ?_⟩
  · unfold sq2
    rw [← Equiv.sum_comp (rootEquiv ι N j h), Fintype.sum_prod_type]
    simp only [pSum, map_sum, map_pow, rename_X, rootEquiv_apply]
  · have hA : (lamA ι N j : Pol ι N) =
        ∑ τ, ∑ i : Fin N, C (cond (decide ((i : ℕ) < j)) (-1 : ℝ) 1) * X (τ, i) := by
      unfold lamA pHigh pLow
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (i : ℕ) < j
      · simp [hi, not_le.mpr hi]
      · simp [hi, not_lt.mp hi]
    rw [hA, rename_rootIdx_lin ι N j h (fun b => cond b (-1 : ℝ) 1)]
    rfl
  · intro al be
    have hI : (invForm j (fun _ : ι => al) (fun _ => be) : Pol ι N) =
        ∑ τ, ∑ i : Fin N, C (cond (decide ((i : ℕ) < j)) al be) * X (τ, i) := by
      unfold invForm pHigh pLow
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (i : ℕ) < j
      · simp [hi, not_le.mpr hi]
      · simp [hi, not_lt.mp hi]
    rw [hI, rename_rootIdx_lin ι N j h (fun b => cond b al be)]

end GlobalTheory.BcEigen
