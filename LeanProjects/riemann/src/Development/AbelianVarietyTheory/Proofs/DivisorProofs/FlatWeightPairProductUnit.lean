import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatUnitInt

theorem vAdd_pow_nat {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K)
    (k : ℕ) : vAdd w (x ^ k) = k * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem one_le_vAdd_int {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {q : 𝓞 K} (hq : (q : K) ≠ 0) (h : q ∈ w.asIdeal) : 1 ≤ vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem (K := K) _).2 h
  have h0 : w.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vAdd
  omega

theorem exists_nat_vAdd {K : Type} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (B : ℝ) :
    ∃ m : ℕ, 0 < m ∧ (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w (m : K)) ∧ ∀ w ∈ S, B ≤ (vAdd w (m : K) : ℝ) := by
  classical
  set N : ℕ := ∏ w ∈ S, Ideal.absNorm w.asIdeal with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  refine ⟨N ^ ⌈B⌉₊, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), fun w => ?_, fun w hw => ?_⟩
  · have := Formalism.L2.Pj.vAdd_int_nonneg w (a := ((N ^ ⌈B⌉₊ : ℕ) : 𝓞 K)) (by have : ((N ^ ⌈B⌉₊ : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0); simpa using this)
    simpa using this
  · have hmem : ((N : ℕ) : 𝓞 K) ∈ w.asIdeal := by
      rw [hN, Nat.cast_prod, ← Finset.mul_prod_erase S _ hw]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem w.asIdeal)
    have h1 : (1 : ℤ) ≤ vAdd w (N : K) := by
      have := one_le_vAdd_int w (q := ((N : ℕ) : 𝓞 K)) (by simpa using hNK) hmem
      simpa using this
    rw [Nat.cast_pow, vAdd_pow_nat]
    push_cast
    have h2 : (1 : ℝ) ≤ (vAdd w (N : K) : ℝ) := by exact_mod_cast h1
    have h3 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    nlinarith [Nat.cast_nonneg (α := ℝ) ⌈B⌉₊]

theorem integral_inverse : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) :=
  GlobalTheory.FlatDenom.unit_pow_denom

end GlobalTheory.FlatUnitInt

end
