import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePowerStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThcAssembly

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ShortClause

theorem val_mul {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vLa la (a * b) = vLa la a + vLa la b := by
  unfold vLa
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem val_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) :
    vLa la (a ^ n) = n * vLa la a := by
  unfold vLa
  rw [map_pow, WithZero.log_pow]
  simp

theorem val_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  unfold vLa
  have h1 : la.valuation K (p : K) ≤ 1 := by
    have := la.valuation_le_one (K := K) (p : 𝓞 K)
    simpa using this
  by_cases h0 : la.valuation K (p : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem thc_le_of_eq_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) = 0) :
    X.Thc s w ≤ B.Mlat j w := by
  intro F hF
  obtain ⟨F1, hF1, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  rw [hsc, zero_smul]
  exact (B.Mlat j w).zero_mem

end ShortClause

open ShortClause in

theorem thc_le_of_shortBound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  intro hSB D T h hs j hj hinj EX hO w a b s ha hb hsE
  by_cases hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) = 0
  · exact thc_le_of_eq_zero (recPJ h j hj) s w hsc
  refine Pf.Thc_le_Mlat (recPJ h j hj) s w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j w) := hG
  have key := Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la))
    (fun g hg => hSB D T h hs j hj hinj EX hO w g hg la y) _ hG'
  refine le_trans ?_ (key.trans (recPJ_vAt_inc h j hj la y w G).ge)
  rw [EReal.coe_le_coe_iff, neg_le_neg_iff]
  set nn : 𝓞 T.Q.c.F := nnW (recB h.toLawsCore) hinj EX w with hnn
  have e : ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) := by
    rw [hsE, zOwnP]
    push_cast
    ring
  have hne : (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) ≠ 0 := by
    rw [← e]
    exact fun h0 => hsc (RingOfIntegers.coe_eq_zero_iff.1 h0)
  have h4 := right_ne_zero_of_mul hne
  have h123 := left_ne_zero_of_mul hne
  have h3 := right_ne_zero_of_mul h123
  have h12 := left_ne_zero_of_mul h123
  have h2 := right_ne_zero_of_mul h12
  have h1 := left_ne_zero_of_mul h12
  have hv : vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F))
      ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      ((DF w + 2 * D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) + vLa la (nn : T.Q.c.F) +
        vLa la ((pPow D a b b : ℕ) : T.Q.c.F) +
        ((D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) := by
    rw [e, val_mul _ h123 h4, val_mul _ h12 h3, val_mul _ h1 h2, val_pow, val_pow]
  have hr := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w a b ha hb
  have hp : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) := by
    exact_mod_cast val_nat_nonneg _ _
  have hk : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
      ((D.R.f : ℝ) * D.R.r * w.n) := mul_nonneg hp (by positivity)
  refine le_trans ?_ (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) hv).symm)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  generalize ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) = x
  push_cast
  nlinarith [hr, hk]

end GlobalTheory.PlaceTop
