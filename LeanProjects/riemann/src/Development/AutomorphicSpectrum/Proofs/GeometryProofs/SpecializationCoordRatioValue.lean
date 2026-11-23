import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DenValue

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem dh_mem_adjoin (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : MRing ι) :
    TiePrimes.dh y c f ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_le_subring (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (A : Subring Ω)
    (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩)) : x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hr j.1 j.2
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem A r
  | add x y _ _ hx hy => exact A.add_mem hx hy
  | mul x y _ _ hx hy => exact A.mul_mem hx hy

theorem hasVal_ratio (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (z ⟨k, i⟩ / z ⟨k, c k⟩) := by
  classical
  unfold Small.HasVal
  refine ⟨Pi.single k 1, Pi.single k 1, MvPolynomial.X ⟨k, i⟩, MvPolynomial.X ⟨k, c k⟩,
    TiePrimes.homog_X _, TiePrimes.homog_X _, fun k' => by simp, ?_, ?_, ?_⟩
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hyc k)]
  · rw [MvPolynomial.aeval_X]
    exact hzc k
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hzc k)]

theorem hasVal_dh (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {h : MRing ι}
    {d : K → ℕ} (hh : IsMultiHomog h d) :
    Small.HasVal y 0 (TiePrimes.dh y c h) z (aeval z h / aeval z (TiePrimes.cMon c d)) := by
  have hc0 : aeval z (TiePrimes.cMon c d) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  unfold Small.HasVal
  refine ⟨d, d, h, TiePrimes.cMon c d, hh, TiePrimes.homog_cMon c d, fun k => by simp, ?_, hc0, ?_⟩
  · rw [TiePrimes.aeval_eq_dh_mul y c hyc hh, TiePrimes.aeval_eq_dh_mul y c hyc (TiePrimes.homog_cMon c d),
      TiePrimes.dh_cMon y c hyc, one_mul]
  · exact (div_mul_cancel₀ _ hc0).symm

private theorem hasVal_eq_of_hasVal_of_le {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {s : Ω} {w w' : 𝕜}
    (h1 : Small.HasVal y 0 s z w) (h2 : Small.HasVal y 0 s z w') : w = w' := by
  have hz' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ mCoordIdeal y, aeval z f = 0 := hz
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzw'⟩ := h2
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hdeq' : dg' = dh' := funext fun k => by
    have := hd' k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hm1 := TiePrimes.homog_mul hg hh'
  have hm2 := TiePrimes.homog_mul hg' hh
  rw [hdeq', ← hdeq, add_comm] at hm2
  have hneg := TiePrimes.homog_mul (TiePrimes.homog_C (K := K) (J := ι) (-1)) hm2
  rw [zero_add] at hneg
  have hF := TiePrimes.homog_add hm1 hneg
  have hFy : aeval y (g * h' + MvPolynomial.C (-1) * (g' * h)) = 0 := by
    simp only [map_add, map_mul, hy, hy', MvPolynomial.aeval_C, map_neg, map_one]
    ring
  have hFz := hz'.2 _ ((TiePrimes.mem_coord_iff y hF).2 hFy)
  simp only [map_add, map_mul, hzw, hzw', MvPolynomial.aeval_C, map_neg, map_one] at hFz
  have hprod : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination hFz
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 (mul_ne_zero hz0 hz0')

theorem value_and_denominator : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  intro K _ ι _ Ω _ y 𝕜 _ z A ev hz hval c hzc hyc hr
  refine ⟨fun k i => hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hr k i⟩) (hasVal_ratio y z c hzc hyc k i), ?_⟩
  intro a
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := hval a
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hbA : TiePrimes.dh y c h ∈ A := adjoin_le_subring y c A hr (dh_mem_adjoin y c h)
  have hc0 : aeval z (TiePrimes.cMon c dh) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  refine ⟨⟨_, hbA⟩, ?_, dh_mem_adjoin y c h, ?_⟩
  · rw [hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hbA⟩) (hasVal_dh y z c hzc hyc hh)]
    exact div_ne_zero hz0 hc0
  · have hab : (a : Ω) * TiePrimes.dh y c h = TiePrimes.dh y c g := by
      have e1 := TiePrimes.aeval_eq_dh_mul y c hyc hg
      have e2 := TiePrimes.aeval_eq_dh_mul y c hyc hh
      rw [hdeq] at e1
      have hP : ∏ k, y ⟨k, c k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
      apply mul_right_cancel₀ hP
      rw [mul_assoc, ← e2, ← e1, hy]
    show (a : Ω) * TiePrimes.dh y c h ∈ _
    rw [hab]
    exact dh_mem_adjoin y c g

end GlobalTheory.CompanionTheory.Ar.DenValue
