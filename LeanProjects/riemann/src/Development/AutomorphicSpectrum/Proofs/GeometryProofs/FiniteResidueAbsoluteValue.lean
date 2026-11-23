import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

theorem mem_range_of_valV_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (h : valV V x ≤ 1) : x ∈ (algebraMap V K').range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one K' x fun v => ?_
  have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
    apply HeightOneSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal v.isMaximal
  rw [hv]
  exact h

theorem valV_algebraMap_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (a : V) : valV V (algebraMap V K' a) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ a

theorem vV_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  have h := WithZero.log_le_log (valV_ne_zero (V := V) hx) (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)
  rw [← h, WithZero.log_one, vV]
  omega

theorem absT_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H l c p _ la T e he hr
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < (e : ℝ) * (ramOverZ la : ℝ) := by
    have h1 : (0 : ℝ) < e := by exact_mod_cast he
    have h2 : (0 : ℝ) < (ramOverZ la : ℝ) := by exact_mod_cast hr
    exact mul_pos h1 h2
  have h0 : FinRd.absT p la T e (0 : T.Fr) = 0 := by simp [FinRd.absT]
  have hne : ∀ x : T.Fr, x ≠ 0 → FinRd.absT p la T e x =
      (p : ℝ) ^ (-((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ)))) := by
    intro x hx
    simp [FinRd.absT, hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    by_cases hx : x = 0
    · subst hx; simp [h0]
    by_cases hy : y = 0
    · subst hy; simp [h0]
    rw [hne _ (mul_ne_zero hx hy), hne _ hx, hne _ hy, vV_mul hx hy, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  · rw [hne _ one_ne_zero]
    have : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [this]
  · intro x hx
    rw [hne _ hx]
    exact Real.rpow_pos_of_pos hp0 _
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [h0]
    rw [hne _ hx, ← Real.rpow_zero (p : ℝ), Real.rpow_le_rpow_left_iff hp]
    have hiff : -((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ))) ≤ 0 ↔ 0 ≤ vV T.V x := by
      rw [neg_nonpos, le_div_iff₀ hd, zero_mul]
      exact_mod_cast Iff.rfl
    rw [hiff, vV_nonneg_iff hx]
    constructor
    · exact mem_range_of_valV_le_one
    · rintro ⟨a, rfl⟩
      exact valV_algebraMap_le_one a

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
