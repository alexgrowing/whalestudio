import Mathlib
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

namespace GlobalTheory.BcEigen.Relabel

private theorem prod_two_blocks {M : Type} [CommMonoid M] {N j : ℕ} (h : j ≤ N) (f : Fin N → M) :
    ∏ x, f x = (∏ i : Fin j, f ⟨i, by have := i.isLt; omega⟩) *
      ∏ i : Fin (N - j), f ⟨j + i, by have := i.isLt; omega⟩ := by
  have h' : j + (N - j) = N := by omega
  rw [← Equiv.prod_comp (finCongr h') f, Fin.prod_univ_add]
  rfl

private theorem rootIdx_low (ι : Type) {N j : ℕ} (τ : ι) (i : Fin j) (hi : (i : ℕ) < N) :
    rootIdx ι N j (τ, ⟨i, hi⟩) = ⟨(τ, true), i⟩ := by
  unfold rootIdx
  rw [dif_pos (show ((⟨i, hi⟩ : Fin N) : ℕ) < j from i.isLt)]
  rfl

private theorem rootIdx_high (ι : Type) {N j : ℕ} (τ : ι) (i : Fin (N - j)) (hi : j + (i : ℕ) < N) :
    rootIdx ι N j (τ, ⟨j + i, hi⟩) = ⟨(τ, false), i⟩ := by
  unfold rootIdx
  rw [dif_neg (show ¬ ((⟨j + i, hi⟩ : Fin N) : ℕ) < j by simp)]
  congr 1
  exact Fin.ext (by simp)

private theorem prod_Ioi_eq_ite {M : Type} [CommMonoid M] {n : ℕ} (i : Fin n) (f : Fin n → M) :
    ∏ b ∈ Finset.Ioi i, f b = ∏ b, if i < b then f b else 1 := by
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext b
  simp

private theorem prod_low_pairs {M : Type} [CommMonoid M] {N j : ℕ} (h : j ≤ N) (g : Fin N → Fin N → M) :
    (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then g a b else 1) =
      ∏ a : Fin j, ∏ b ∈ Finset.Ioi a,
        g ⟨a, by have := a.isLt; omega⟩ ⟨b, by have := b.isLt; omega⟩ := by
  rw [prod_two_blocks h]
  have h2 : (∏ i : Fin (N - j), ∏ b : Fin N,
      if (⟨j + i, by have := i.isLt; omega⟩ : Fin N) < b ∧ (b : ℕ) < j then
        g ⟨j + i, by have := i.isLt; omega⟩ b else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun b _ => if_neg ?_
    rw [Fin.lt_def]
    simp only
    omega
  rw [h2, mul_one]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [prod_two_blocks h, prod_Ioi_eq_ite]
  rw [Finset.prod_eq_one (s := (Finset.univ : Finset (Fin (N - j)))), mul_one]
  · refine Finset.prod_congr rfl fun b _ => if_congr ?_ rfl rfl
    have := b.isLt
    rw [Fin.lt_def, Fin.lt_def]
    simp only
    omega
  · intro b _
    exact if_neg (by simp)

private theorem prod_high_pairs {M : Type} [CommMonoid M] {N j : ℕ} (h : j ≤ N) (g : Fin N → Fin N → M) :
    (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then g a b else 1) =
      ∏ a : Fin (N - j), ∏ b ∈ Finset.Ioi a,
        g ⟨j + a, by have := a.isLt; omega⟩ ⟨j + b, by have := b.isLt; omega⟩ := by
  rw [prod_two_blocks h]
  have h2 : (∏ i : Fin j, ∏ b : Fin N,
      if (⟨i, by have := i.isLt; omega⟩ : Fin N) < b ∧ j ≤ (i : ℕ) then
        g ⟨i, by have := i.isLt; omega⟩ b else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun b _ => if_neg ?_
    have := i.isLt
    omega
  rw [h2, one_mul]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [prod_two_blocks h, prod_Ioi_eq_ite]
  rw [Finset.prod_eq_one (s := (Finset.univ : Finset (Fin j))), one_mul]
  · refine Finset.prod_congr rfl fun b _ => if_congr ?_ rfl rfl
    rw [Fin.lt_def, Fin.lt_def]
    simp only
    omega
  · intro b _
    refine if_neg ?_
    have := b.isLt
    rw [Fin.lt_def]
    simp only
    omega

private theorem rename_fibPt (ι : Type) [Fintype ι] (N j : ℕ) (h : j ≤ N) :
    rename (rootIdx ι N j) (fibPt ι N j) = ∏ a, monPt (rkB ι N j) a := by
  unfold GlobalTheory.FlagPoly.fibPt
  rw [map_prod, Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fintype.prod_bool, prod_two_blocks h]
  congr 1
  · unfold monPt
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_neg, rename_X, rootIdx_low, if_pos (show ((i : ℕ)) < j from i.isLt)]
    rfl
  · unfold monPt
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_neg, rename_X, rootIdx_high, if_neg (by simp)]
    congr 1
    show N - 1 - (j + (i : ℕ)) = N - j - 1 - (i : ℕ)
    omega

private theorem rename_vdmCl (ι : Type) [Fintype ι] (N j : ℕ) (h : j ≤ N) :
    rename (rootIdx ι N j) (vdmCl ι N j) =
      ∏ a, (C ((rkB ι N j a).factorial : ℝ)⁻¹ * vdm (rkB ι N j) a) := by
  unfold vdmCl
  rw [map_prod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fintype.prod_bool, prod_low_pairs h (fun a b => (X (τ, b) - X (τ, a) : Pol ι N)),
    prod_high_pairs h (fun a b => (X (τ, b) - X (τ, a) : Pol ι N))]
  simp only [map_mul, map_prod, map_sub, rename_C, rename_X, rootIdx_low, rootIdx_high]
  rfl

private theorem relabel_prods (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (h : j ≤ N) :
    rename (rootIdx ι N j) (fibPt ι N j) = ∏ a, monPt (rkB ι N j) a ∧
    rename (rootIdx ι N j) (vdmCl ι N j) =
      ∏ a, (C ((rkB ι N j a).factorial : ℝ)⁻¹ * vdm (rkB ι N j) a) :=
  ⟨rename_fibPt ι N j h, rename_vdmCl ι N j h⟩

end GlobalTheory.BcEigen.Relabel

theorem _root_.GlobalTheory.T.relabel_fibre_point_vandermonde_product : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), j ≤ N →
    rename (rootIdx ι N j) (fibPt ι N j) = ∏ a, monPt (rkB ι N j) a ∧
    rename (rootIdx ι N j) (vdmCl ι N j) = ∏ a, (C ((rkB ι N j a).factorial : ℝ)⁻¹ * vdm (rkB ι N j) a) :=
  fun ι _ _ N j h => GlobalTheory.BcEigen.Relabel.relabel_prods ι N j h
