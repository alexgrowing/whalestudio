import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.HermLB

namespace GlobalTheory.FlagZ.WeightDrop

theorem sum_smul_sub {G : Type*} [AddCommGroup G] {N : ℕ} (F : Fin (N + 1) → G) (m : Fin N → ℤ) :
    ∑ i : Fin N, m i • (F i.castSucc - F i.succ) =
      ∑ l : Fin (N + 1), ((if h : (l : ℕ) < N then m ⟨l, h⟩ else 0) -
        (if h : 0 < (l : ℕ) then m ⟨l - 1, by have := l.isLt; omega⟩ else 0)) • F l := by
  simp only [smul_sub, Finset.sum_sub_distrib, sub_smul]
  congr 1
  · rw [Fin.sum_univ_castSucc]
    simp
  · rw [Fin.sum_univ_succ]
    simp

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem isometric_pull_congr (L : HermLB p) {f f' : Y ⟶ X} (hf : f ≫ p = q) (hf' : f' ≫ p = q) (e : f = f') :
    (L.pull f hf).Isometric (L.pull f' hf') := by
  subst e
  exact Isometric.refl _

theorem isometric_of_refines {N L : HermLB p} {π : N.B.ι → L.B.ι} (h : GlobalTheory.TwistTop.Refines N L π 0) :
    N.Isometric L :=
  isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

end GlobalTheory.FlagZ.WeightDrop

namespace GlobalTheory.FlagZ.WeightDrop

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem isometric_pull_detDual (x : ι × Fin (N + 1)) (y : {y // y ≠ x}) :
    ((detDual (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2) y).pull (forget x) (toZ_ext _ _)).Isometric
      (flDet y.1.1 y.1.2) := by
  refine (isometric_of_refines (HermLB.refines_pull_pull _ _ _ (forget x) (toZ_ext _ _) (toZ_ext _ _))).trans ?_
  exact isometric_pull_congr _ _ _ (comap_plEmb_π _ _ _ _ _ _ y)

end GlobalTheory.FlagZ.WeightDrop

namespace GlobalTheory.FlagZ.WeightDrop

variable {ι : Type} [Fintype ι] {N : ℕ}

def coef (lam : ι → Fin N → ℤ) (y : ι × Fin (N + 1)) : ℤ :=
  (if h : (y.2 : ℕ) < N then -lam y.1 ⟨y.2, h⟩ else 0) -
    (if h : 0 < (y.2 : ℕ) then -lam y.1 ⟨y.2 - 1, by have := y.2.isLt; omega⟩ else 0)

theorem icls_wtLine (lam : ι → Fin N → ℤ) :
    (wtLine lam).icls = ∑ y : ι × Fin (N + 1), coef lam y • (flDet y.1 y.2).icls := by
  rw [wtLine, icls_comb, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [grLine, icls_tens, icls_dual, ← sub_eq_add_neg]
  exact sum_smul_sub (fun l => (flDet τ l).icls) (fun i => -lam τ i)

open Classical in

theorem isometric_wtLine_pull (lam : ι → Fin N → ℤ) (x : ι × Fin (N + 1)) (hx : coef lam x = 0) :
    (wtLine lam).Isometric ((comb (detDual (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2))
      fun y => coef lam y.1).pull (forget x) (toZ_ext _ _)) := by
  classical
  refine icls_eq_iff.1 ?_
  rw [icls_wtLine, icls_pull, icls_comb, map_sum, Fintype.sum_eq_add_sum_subtype_ne _ x, hx, zero_smul, zero_add]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_zsmul, ← icls_pull, icls_eq_iff.2 (isometric_pull_detDual x y)]

theorem coef_eq_zero (lam : ι → Fin N → ℤ) (τ : ι) (j : ℕ) (h₁ : 1 ≤ j) (h₂ : j < N)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) = j → lam τ a = lam τ b) :
    coef lam (τ, ⟨j, by omega⟩) = 0 := by
  have e := h ⟨j - 1, by omega⟩ ⟨j, h₂⟩ (by simp; omega) rfl
  simp only [coef, dif_pos h₂, dif_pos (show 0 < j by omega)]
  rw [e]
  ring

theorem dim_closure_lt (x : ι × Fin (N + 1)) (h₀ : 0 < (x.2 : ℕ)) (h₁ : (x.2 : ℕ) < N) :
    topologicalKrullDim (closure ({forget x (genericPoint (Fl ι N))} : Set (FlOmit x))) < ((dimFl ι N + 1 : ℕ) : WithBot ℕ∞) := by
  refine (topologicalKrullDim_subspace_le _ _).trans_lt ?_
  rw [(smooth_dim_isArithVar_part ι {y // y ≠ x} N (fun y => y.1.1) (fun y => y.1.2)).2.1,
    (Count.card_cellVar ι N).2.2 x h₀ h₁]
  exact_mod_cast Nat.lt_succ_self _

end GlobalTheory.FlagZ.WeightDrop
