import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.BoxProd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem mul_mem_Bl (P : Pair p) {a b a' b' : ℤ} {R R' : ℝ} (hR : 0 ≤ R) {f g : X.functionField}
    (hf : f ∈ P.Bl a b R) (hg : g ∈ P.Bl a' b' R') : f * g ∈ P.Bl (a + a') (b + b') (R * R') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul _ _ _ P a b a' b' f g hf.1 hg.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2 σ y]
  exact mul_le_mul (hf.2 σ y) (hg.2 σ y) (nu_nonneg _ _ _ _ _ _) hR

theorem one_mem_Bl (P : Pair p) : (1 : X.functionField) ∈ P.Bl 0 0 1 := by
  refine ⟨fun x i j _ _ => ?_, fun σ y => ?_⟩
  · simp only [Pair.loc, zpow_zero, mul_one]
    exact ⟨1, map_one _⟩
  · have e := IntExample.ratVal_nat y 1
    simp only [Nat.cast_one] at e
    simp [Pair.nu, Pair.loc, e]

theorem prod_mem_of_le (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField)
    (a b : ℤ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ c, boxFam e x c ∈ P.Bl a b R) :
    ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i ≤ m) →
      (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro m
  induction m with
  | zero =>
    intro u n hn
    have h0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
    simp only [h0, pow_zero, Finset.prod_const_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Nat.cast_zero, zero_mul]
    exact one_mem_Bl P
  | succ m ih =>
    intro u n hn
    have hx : ∏ i, x i ^ n i =
        (∏ i ∈ Finset.univ.filter (fun i => 0 < n i), x i) * ∏ i, x i ^ (n i - 1) := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases Nat.eq_zero_or_pos (n i) with h0 | h0
      · simp [h0]
      · rw [if_pos h0, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n i)]
    have key : (∏ l, e (u l)) * ∏ i, x i ^ n i =
        boxFam e x (u 0, Finset.univ.filter (fun i => 0 < n i)) *
          ((∏ l : Fin m, e (u l.succ)) * ∏ i, x i ^ (n i - 1)) := by
      rw [Fin.prod_univ_succ, hx]
      simp only [boxFam]
      ring
    rw [key]
    have hm := mul_mem_Bl P hR (h (u 0, Finset.univ.filter (fun i => 0 < n i)))
      (ih (fun l => u l.succ) (fun i => n i - 1) (fun i => by have := hn i; omega))
    have ea : ((m + 1 : ℕ) : ℤ) * a = a + m * a := by push_cast; ring
    have eb : ((m + 1 : ℕ) : ℤ) * b = b + m * b := by push_cast; ring
    rw [ea, eb, pow_succ']
    exact hm

theorem prod_mem_Bl : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro k _ X _ p P D J e x a b R hR h m u n hn
  exact prod_mem_of_le P D J e x a b R hR h m u n fun i => (hn i).le

end GlobalTheory.HSNef.BoxProd
