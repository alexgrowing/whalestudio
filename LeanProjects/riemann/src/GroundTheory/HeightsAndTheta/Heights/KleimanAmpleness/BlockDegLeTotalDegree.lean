import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ChartKernel

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type}

abbrev blockDeg (e : (Σ k, ι k) →₀ ℕ) : K →₀ ℕ := e.mapDomain Sigma.fst

theorem prod_block_pow {R : Type} [CommMonoid R] (e : (Σ k, ι k) →₀ ℕ) (v : K → R) :
    (e.prod fun p n => v p.1 ^ n) = ∏ k, v k ^ blockDeg e k := by
  have h := Finsupp.prod_mapDomain_index (f := Sigma.fst) (s := e) (h := fun k n => v k ^ n)
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  exact h.symm.trans (Finsupp.prod_fintype _ _ (fun _ => pow_zero _))

omit [Fintype K] in

theorem blockDeg_le_totalDegree (g : MvPolynomial (Σ k, ι k) S) :
    ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ g.totalDegree := by
  intro e he k
  refine le_trans ?_ (le_totalDegree he)
  rw [← Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases hk : k ∈ (blockDeg e).support
  · exact Finset.single_le_sum (f := fun k => blockDeg e k) (fun _ _ => Nat.zero_le _) hk
  · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _

def homog (c : ∀ k, ι k) (D : ℕ) (g : MvPolynomial (Σ k, ι k) S) : MvPolynomial (Σ k, ι k) S :=
  ∑ e ∈ g.support, monomial e (coeff e g) * ∏ k, X ⟨k, c k⟩ ^ (D - blockDeg e k)

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem mConeMapOver_monomial (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : S) :
    mConeMapOver S y (monomial e a) = C (aeval y (monomial e a)) * ∏ k, X k ^ blockDeg e k := by
  simp only [mConeMapOver, aeval_monomial, mul_pow, Finsupp.prod_mul]
  rw [prod_block_pow e (fun k => (X k : MvPolynomial K Ω))]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem mConeMapOver_homog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {D : ℕ} {g : MvPolynomial (Σ k, ι k) S}
    (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    mConeMapOver S y (homog c D g) = C (aeval y (homog c D g)) * ∏ k, X k ^ D := by
  simp only [homog, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ k, (X k : MvPolynomial K Ω) ^ D =
      (∏ k, X k ^ blockDeg e k) * ∏ k, X k ^ (D - blockDeg e k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.add_sub_cancel' (hD e he k)]
  rw [map_mul, mConeMapOver_monomial, hX]
  simp only [map_mul, map_prod, map_pow, mConeMapOver, aeval_X, mul_pow, Finset.prod_mul_distrib]
  ring

theorem aeval_homog (w : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) {D : ℕ}
    {g : MvPolynomial (Σ k, ι k) S} (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    aeval w (homog c D g) = (∏ k, w ⟨k, c k⟩ ^ D) * aeval (fun p => w p / w ⟨p.1, c p.1⟩) g := by
  conv_rhs => rw [g.as_sum]
  simp only [homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hP : ∏ k, w ⟨k, c k⟩ ^ D =
      (∏ k, w ⟨k, c k⟩ ^ (D - blockDeg e k)) * ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.sub_add_cancel (hD e he k)]
  have hne : ∏ k, w ⟨k, c k⟩ ^ blockDeg e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k)
  have hq : (e.prod fun p n => (w p / w ⟨p.1, c p.1⟩) ^ n) =
      (e.prod fun p n => w p ^ n) / ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← prod_block_pow e (fun k => w ⟨k, c k⟩)]
    simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib]
  rw [map_mul, aeval_monomial, aeval_monomial, hq, hP]
  simp only [map_prod, map_pow, aeval_X]
  field_simp

end ChartKernel

theorem ChartKernel.proof : ChartKernel.Statement := by
  intro S _ K _ _ ι Ω _ _ y Ω' _ _ y' hle c hc g hg
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    have hm : (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
      change mConeMapOver S y (X _) = 0
      simp [mConeMapOver, h0]
    have h' : mConeMapOver S y' (X ⟨k, c k⟩) = 0 := hle hm
    simpa [mConeMapOver, X_ne_zero] using h')
  have hD := ChartKernel.blockDeg_le_totalDegree g
  have h1 : aeval y (ChartKernel.homog c g.totalDegree g) = 0 := by
    rw [ChartKernel.aeval_homog y hyc hD, hg, mul_zero]
  have h2 : ChartKernel.homog c g.totalDegree g ∈ mIdealOver S y := by
    change mConeMapOver S y _ = 0
    rw [ChartKernel.mConeMapOver_homog y c hD, h1, map_zero, zero_mul]
  have h3 : mConeMapOver S y' (ChartKernel.homog c g.totalDegree g) = 0 := hle h2
  rw [ChartKernel.mConeMapOver_homog y' c hD] at h3
  have h4 : aeval y' (ChartKernel.homog c g.totalDegree g) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact C_eq_zero.mp h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))
  rw [ChartKernel.aeval_homog y' hc hD] at h4
  exact (mul_eq_zero.mp h4).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
