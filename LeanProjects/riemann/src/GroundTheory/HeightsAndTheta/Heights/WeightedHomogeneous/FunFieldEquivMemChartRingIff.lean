import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def funFieldEquiv (P : ArithVariety n) : P.FunField ≃+* FunField P :=
  (IsLocalization.algEquiv (nonZeroDivisors (CoordRing P)) P.FunField (FunField P)).toRingEquiv

omit [Fintype ι] in
theorem funFieldEquiv_algebraMap (P : ArithVariety n) (r : CoordRing P) :
    funFieldEquiv P (algebraMap (CoordRing P) P.FunField r) =
      algebraMap (CoordRing P) (FunField P) r :=
  (IsLocalization.algEquiv (nonZeroDivisors (CoordRing P)) P.FunField (FunField P)).commutes r

omit [Fintype ι] in

theorem funFieldEquiv_mkF (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) :
    funFieldEquiv P (P.mkF f) = val P f :=
  funFieldEquiv_algebraMap P _

omit [Fintype ι] in

theorem funFieldEquiv_mkF_X (P : ArithVariety n) (v : Coord n) :
    funFieldEquiv P (P.mkF (X v)) = genPt P v :=
  funFieldEquiv_mkF P _

omit [Fintype ι] in

theorem funFieldEquiv_chartCoord (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funFieldEquiv P (P.chartCoord c v) = genPt P v / genPt P ⟨v.1, c v.1⟩ := by
  rw [ArithVariety.chartCoord, map_div₀, funFieldEquiv_mkF_X, funFieldEquiv_mkF_X]

omit [Fintype ι] in

theorem funFieldEquiv_image_chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) :
    funFieldEquiv P '' (P.chartRing c : Set P.FunField) = (chartRing P c : Set (FunField P)) := by
  have hmap := RingHom.map_closure (funFieldEquiv P).toRingHom (Set.range (P.chartCoord c))
  have hrange : (funFieldEquiv P).toRingHom '' Set.range (P.chartCoord c) =
      Set.range fun p : Coord n ↦ genPt P p / genPt P ⟨p.1, c p.1⟩ := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact funFieldEquiv_chartCoord P c v
  rw [hrange] at hmap
  rw [chartRing, ReciprocityTheory.ChartRestriction.G.Geo.chartRingZ, Algebra.adjoin_int, ← hmap]
  rfl

omit [Fintype ι] in

theorem funFieldEquiv_mem_chartRing_iff (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (x : P.FunField) : funFieldEquiv P x ∈ chartRing P c ↔ x ∈ P.chartRing c := by
  rw [← SetLike.mem_coe, ← funFieldEquiv_image_chartRing]
  exact (funFieldEquiv P).injective.mem_set_image

theorem funFieldEquiv_chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funFieldEquiv P (P.chartPow c a) = chartPow P c a := by
  rw [ArithVariety.chartPow, chartPow, map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, funFieldEquiv_mkF_X]

theorem chartPow_neg (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    chartPow P c (-a) = (chartPow P c a)⁻¹ := by
  rw [chartPow, chartPow, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Pi.neg_apply, zpow_neg]

theorem funFieldEquiv_div_chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ)
    (x : P.FunField) :
    funFieldEquiv P (x / P.chartPow c a) = funFieldEquiv P x * chartPow P c (-a) := by
  rw [map_div₀, funFieldEquiv_chartPow, chartPow_neg, div_eq_mul_inv]

omit [Fintype ι] in

theorem isOfDegree_iff (P : ArithVariety n) (a : ι → ℤ) (x : P.FunField) :
    P.IsOfDegree a x ↔ IsHomogOfDeg P a (funFieldEquiv P x) := by
  constructor
  · rintro ⟨f, g, df, dg, hf, hg, hd, hgP, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hgP, hd, ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
  · rintro ⟨f, g, df, dg, hf, hg, hgP, hd, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hd, hgP, (funFieldEquiv P).injective ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]

def GenSystem.ofIsHomogGenerators {P : ArithVariety n} {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (h : P.IsHomogGenerators G δ) :
    GenSystem P where
  r := r
  f := G
  δ := δ
  homog := h.homog
  span_eq := h.span_eq

omit [Fintype ι] in

theorem GenSystem.isHomogGenerators {P : ArithVariety n} (Γ : GenSystem P) :
    P.IsHomogGenerators Γ.f Γ.δ :=
  ⟨Γ.homog, Γ.span_eq⟩

def genSystemEquiv (P : ArithVariety n) :
    GenSystem P ≃ Σ r : ℕ, {p : (Fin r → MvPolynomial (Coord n) ℤ) × (Fin r → ι → ℕ) //
      P.IsHomogGenerators p.1 p.2} where
  toFun Γ := ⟨Γ.r, (Γ.f, Γ.δ), Γ.isHomogGenerators⟩
  invFun p := GenSystem.ofIsHomogGenerators p.2.2
  left_inv _ := rfl
  right_inv _ := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
