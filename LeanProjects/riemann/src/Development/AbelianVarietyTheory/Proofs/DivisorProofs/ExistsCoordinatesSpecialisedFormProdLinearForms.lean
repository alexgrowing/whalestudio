import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SplitCoord

theorem map_spec {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] {D N : ℕ} (s : Fin D → Fin N → E) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    map (algebraMap E K) (spec s f) = spec (fun i j => algebraMap E K (s i j)) f := by
  unfold spec
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X]
    congr 1
    obtain ⟨a, b⟩ := i
    refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [join]

theorem map_lin_smul {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) {N : ℕ} (c : E) (y : Fin N → E) :
    map φ (lin (c • y)) = C (φ c) * lin fun j => φ (y j) := by
  simp only [lin, map_sum, map_mul, map_X, map_C, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_eq_C_mul {E K σ : Type} [Field E] [Field K] (φ : E →+* K) {P Q : MvPolynomial σ E} (hP : P ≠ 0) {c : K}
    (hc : c ≠ 0) (h : map φ Q = C c * map φ P) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * P := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP
  have e : φ (coeff m Q) = c * φ (coeff m P) := by
    simpa only [coeff_map, coeff_C_mul] using congrArg (coeff m) h
  have e' : φ (coeff m Q / coeff m P) = c := by
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero φ).2 hm)]
  refine ⟨coeff m Q / coeff m P, fun h0 => hc (by rw [← e', h0, map_zero]), map_injective φ φ.injective ?_⟩
  rw [map_mul, map_C, e', h]

theorem exists_eq_C_mul_prod {E K ι : Type} [Field E] [Field K] [Fintype ι] (φ : E →+* K) {N : ℕ}
    {Q : MvPolynomial (Fin 1 × Fin N) E} {y v : ι → Fin N → E} {z : ι → Fin N → K} {a : ι → E} (hy : ∀ p, y p ≠ 0)
    (ha : ∀ p, a p ≠ 0) (ea : ∀ p, y p = a p • v p) (hz : ∀ p, z p = fun j => φ (v p j)) {c : K} (hc : c ≠ 0)
    (h : map φ Q = C c * ∏ p, lin (z p)) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * ∏ p, lin (y p) := by
  have hA : (∏ p, φ (a p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => (map_ne_zero _).2 (ha p)
  refine exists_eq_C_mul φ (Finset.prod_ne_zero_iff.2 fun p _ => Check.lin_ne (hy p)) (div_ne_zero hc hA) ?_
  rw [h, map_prod]
  simp only [ea, hz, map_lin_smul]
  rw [Finset.prod_mul_distrib, ← map_prod C, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hA]

theorem exists_coord_spec_eq : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  intro F _ _ G E _ _ _ s hs δ f h hS
  obtain rfl := hS.card
  obtain ⟨x, Co, hCo, -⟩ := h.exists_coord hs
  obtain ⟨c, hc, e⟩ := hS.fac
  choose a ha ea using fun p => G.exists_coords_baseChange E (x p).pt.1
  have h₅ (p) : G.coords (LinSys.toBase (RatPt.geomPt G E s (x p))).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords ((x p).pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  have h₇ : ∏ᶠ z ∈ G.geomPts E (G.linSection E s), lin (G.coords (LinSys.toBase z : G.Pt (AlgebraicClosure E)).1) =
      ∏ p, lin (G.coords (LinSys.toBase (RatPt.geomPt G E s (x p)) : G.Pt (AlgebraicClosure E)).1) := by
    refine (finprod_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
    rw [finprod_mem_range (RatPt.geomPt_injective hs), ← finprod_comp_equiv x, finprod_eq_prod_of_fintype]
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_C_mul_prod (N := G.N) (algebraMap E (AlgebraicClosure E)) (Q := spec s f) (y := Co.y)
    (fun p h0 => (G.baseChange E).geom.alg.bpf.coords_ne_zero _ ((hCo p).2.1.symm.trans h0)) ha
    (fun p => (hCo p).2.1.trans (ea p)) h₅ hc ((map_spec s f).trans (e.trans (congrArg (C c * ·) h₇)))
  exact ⟨Co, c₀, h₀, e₀⟩

end GlobalTheory.HSShort.SplitCoord
