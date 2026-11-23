import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializes
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoOrd

variable {Y : Scheme.{0}} [IsIntegral Y]

def schOrdHom [IsLocallyNoetherian Y] (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem schOrd_prod_zpow [IsLocallyNoetherian Y] {ι : Type} (s : Finset ι)
    (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ s, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ s, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (schOrdHom v) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

theorem schOrd_inv [IsLocallyNoetherian Y] (g : Y.functionFieldˣ) (v : Y) :
    Scheme.ord ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) v =
      - Scheme.ord (g : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_inv (schOrdHom v) g)
  rw [toAdd_inv] at h
  exact h

variable {k : Type} [Field k] {q : Y ⟶ Sp k}

def divOrdHom (E : DivOver q) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (E.ord g)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul, ofAdd_add]

theorem divOrd_prod_zpow (E : DivOver q) {ι : Type} (s : Finset ι) (u : ι → Y.functionFieldˣ)
    (m : ι → ℤ) : E.ord (∏ j ∈ s, u j ^ m j) = ∑ j ∈ s, m j * E.ord (u j) := by
  have h := congrArg Multiplicative.toAdd (map_prod (divOrdHom E) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

end GlobalTheory.Discrepancy.MonoOrd

open GlobalTheory.Discrepancy.MonoOrd in

theorem GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  intro k _ Y _ _ _ q E y hE ι _ w u hw _ _ hself hother φ hφ
  classical
  set a : ι → ℤ := fun j => Scheme.ord (φ : Y.functionField) (w j) with ha
  set ψ : Y.functionFieldˣ := φ * ∏ j, u j ^ (-a j) with hψ
  have hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (ψ : Y.functionField) v = 0 := by
    intro v hv h1
    rw [hψ, Units.val_mul, Scheme.ord_mul φ.ne_zero (Units.ne_zero _), schOrd_prod_zpow]
    by_cases h : ∃ i, v = w i
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · rw [hself i, ha]
        ring
      · intro j _ hji
        rw [hother j (w i) hv h1 (fun e => hji (hw e.symm)), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => by rw [hother j v hv h1 (h j), mul_zero],
        hφ v hv h1 h, add_zero]
  have hreg : ∀ g : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : Y.functionField) v = 0) →
        0 ≤ E.ord g := fun g hg =>
    (E.ord_nonneg_iff g).2 (hE _ (regAt_of_forall_coheight_eq_one fun z hz h1 =>
      (GlobalTheory.RegCodimOne.regAt_iff_ord_nonneg h1 g.ne_zero).2 (hg z hz h1).ge))
  have h0 := hreg ψ hord
  have h0' := hreg ψ⁻¹ fun v hv h1 => by rw [schOrd_inv, hord v hv h1, neg_zero]
  rw [E.ord_inv] at h0'
  have hψ0 : E.ord ψ = 0 := by omega
  rw [hψ, E.ord_mul, divOrd_prod_zpow] at hψ0
  simp only [neg_mul, Finset.sum_neg_distrib] at hψ0
  rw [ha] at hψ0
  linarith
