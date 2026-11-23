import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

def chartIdeal (w : (Σ k, J k) → K) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (U : Ideal (MRing J)) :
    Ideal (chartRingZ w c) where
  carrier := {r | (r : K) ∈ chartPrime w c U}
  add_mem' ha hb := chartPrime_add w ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, U.zero_mem, by simp⟩
  smul_mem' a _ hb := chartPrime_mul w hc a.2 hb

theorem mem_chartIdeal {w : (Σ k, J k) → K} {c : ∀ k, J k} {hc : ∀ k, w ⟨k, c k⟩ ≠ 0} {U : Ideal (MRing J)}
    {r : chartRingZ w c} : r ∈ chartIdeal w c hc U ↔ (r : K) ∈ chartPrime w c U :=
  Iff.rfl

theorem chartIdeal_mono {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U U' : Ideal (MRing J)} (h : U ≤ U') : chartIdeal w c hc U ≤ chartIdeal w c hc U' := by
  rintro r ⟨e, g, hg, hgU, hr⟩
  exact ⟨e, g, hg, h hgU, hr⟩

theorem chartIdeal_isPrime (w : (Σ k, J k) → K) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U : Ideal (MRing J)} (hVU : mCoordIdeal w ≤ U) (hU : U.IsPrime)
    (hXU : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ U) : (chartIdeal w c hc U).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff w hVU hU hXU (r := ((1 : chartRingZ w c) : K)) (e := 0) (k := 1)
      GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartIdeal.mp h)
    exact hU.ne_top ((Ideal.eq_top_iff_one U).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep w hc a.2
    obtain ⟨e', k', hk', hb⟩ := exists_rep w hc b.2
    have hkk : k * k' ∈ U := (mem_chartPrime_iff w hVU hU hXU (r := ((a * b : chartRingZ w c) : K))
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [MulMemClass.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : K) * ∏ k, w ⟨k, c k⟩ ^ e' k) * ha + (aeval w k) * hb)).mp
      (mem_chartIdeal.mp hab)
    rcases hU.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem mem_minimalPrimes_of_coord (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K)
    (hbir : Birational w) (W : Ideal (MRing J)) (c : ∀ k, J k) (hWp : W.IsPrime) (hWh : IsMultiHomogIdeal W)
    (hVW : mCoordIdeal w ≤ W) (hXc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) (c₀ : J k)
    (hw : w ⟨k, c₀⟩ ≠ 0) (hx : (X ⟨k, c₀⟩ : MRing J) ∈ W) :
    W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  classical
  have hIW : mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)} ≤ W :=
    sup_le hVW ((Ideal.span_singleton_le_iff_mem _).2 hx)
  refine ⟨⟨hWp, hIW⟩, ?_⟩
  rintro Q ⟨hQp, hIQ⟩ hQW
  have hwc : ∀ j, w ⟨j, c j⟩ ≠ 0 := fun j h => hXc j (hVW ((X_mem_iff w j (c j)).2 h))
  have hVQ : mCoordIdeal w ≤ Q := le_sup_left.trans hIQ
  have hxQ : (X ⟨k, c₀⟩ : MRing J) ∈ Q := hIQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hXQ : ∀ j, (X ⟨j, c j⟩ : MRing J) ∉ Q := fun j h => hXc j (hQW h)

  have hpW := chartIdeal_isPrime w hwc hVW hWp hXc
  have hpQ := chartIdeal_isPrime w hwc hVQ hQp hXQ

  let r : chartRingZ w c := ⟨w ⟨k, c₀⟩ / w ⟨k, c k⟩, Algebra.subset_adjoin ⟨⟨k, c₀⟩, rfl⟩⟩
  have hr : r ∈ chartIdeal w c hwc Q := by
    refine ⟨Pi.single k 1, X ⟨k, c₀⟩, GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c₀, hxQ, ?_⟩
    have hprod : ∏ j, w ⟨j, c j⟩ ^ (Pi.single k 1 : B → ℕ) j = w ⟨k, c k⟩ := by
      rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_eq_of_ne hj])]
      simp
    rw [hprod, aeval_X]
    exact div_mul_cancel₀ _ (hwc k)
  have hne : chartIdeal w c hwc Q ≠ ⊥ := by
    intro h0
    have h1 : r = 0 := by simpa [h0] using hr
    exact div_ne_zero hw (hwc k) (congrArg Subtype.val h1)
  have hmax := chart_prime_isMaximal (p := p) w hbir c hwc _ hpQ hne
  have heq := hmax.eq_of_le hpW.ne_top (chartIdeal_mono hwc hQW)

  obtain ⟨S, hS, hSe⟩ := hWh
  have hSW : Ideal.span S ≤ W := hSe.ge
  rw [hSe, Ideal.span_le]
  intro g hg
  obtain ⟨e, he⟩ := hS g hg
  have hprod : (∏ j, w ⟨j, c j⟩ ^ e j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hwc j)
  have hrep : aeval w g * (∏ j, w ⟨j, c j⟩ ^ e j)⁻¹ * ∏ j, w ⟨j, c j⟩ ^ e j = aeval w g :=
    inv_mul_cancel_right₀ hprod _
  let t : chartRingZ w c := ⟨_, form_div_mem_chart w c he⟩
  have htW : t ∈ chartIdeal w c hwc W := ⟨e, g, he, hSW (Ideal.subset_span hg), hrep⟩
  rw [← heq] at htW
  exact (mem_chartPrime_iff w hVQ hQp hXQ he hrep).1 (mem_chartIdeal.1 htW)

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

end
