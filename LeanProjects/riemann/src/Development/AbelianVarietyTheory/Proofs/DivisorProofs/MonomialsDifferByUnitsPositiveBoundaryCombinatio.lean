import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem coneval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  intro V _ _ _ r m N n hn ε s₁ s₂ ga h1m h1u h2m h2u hprod
  classical
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  let ℓ : FractionRing V → ℤ := fun x => WithZero.log (v x)
  have hinj := IsFractionRing.injective V (FractionRing V)
  have hne : ∀ x : V, x ≠ 0 → algebraMap V (FractionRing V) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ hinj).2 hx
  have hv0 : ∀ x : FractionRing V, x ≠ 0 → v x ≠ 0 := fun x hx => (Valuation.ne_zero_iff v).2 hx
  have ℓmul : ∀ x y : FractionRing V, x ≠ 0 → y ≠ 0 → ℓ (x * y) = ℓ x + ℓ y := fun x y hx hy => by
    simp only [ℓ, map_mul, WithZero.log_mul (hv0 x hx) (hv0 y hy)]
  have ℓzpow : ∀ (x : FractionRing V) (z : ℤ), ℓ (x ^ z) = z * ℓ x := fun x z => by
    simp only [ℓ, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  have ℓprod : ∀ (J : Type) (t : Finset J) (g : J → FractionRing V), (∀ i, g i ≠ 0) →
      ℓ (∏ i ∈ t, g i) = ∑ i ∈ t, ℓ (g i) := by
    intro J t g hg
    induction t using Finset.induction_on with
    | empty => simp [ℓ]
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ℓmul _ _ (hg j)
        (Finset.prod_ne_zero_iff.2 fun i _ => hg i), ih]
  have hunit : ∀ x : V, IsUnit x → ℓ (algebraMap V (FractionRing V) x) = 0 := by
    intro x hx
    have h1 : v (algebraMap V (FractionRing V) x) = 1 := by
      refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ x) ?_
      by_contra hlt
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).1 (lt_of_not_ge hlt)
      exact (IsLocalRing.mem_maximalIdeal x).1 this hx
    simp only [ℓ, h1, WithZero.log_one]
  have hneg : ∀ x : V, x ∈ maximalIdeal V → x ≠ 0 → ℓ (algebraMap V (FractionRing V) x) < 0 := by
    intro x hm hx
    have h1 : v (algebraMap V (FractionRing V) x) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).2 hm
    have := (WithZero.log_lt_log (hv0 _ (hne x hx)) one_ne_zero).2 h1
    simpa [ℓ, WithZero.log_one] using this
  have hs0 : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ i, algebraMap V (FractionRing V) (s i) ≠ 0 := by
    intro s hm hu i
    rcases i with k | k
    · exact hne _ (hm k).2
    · exact hne _ (hu k).ne_zero
  have hsum : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ z : (Fin m ⊕ Fin N) → ℤ,
      ℓ (∏ i, algebraMap V (FractionRing V) (s i) ^ z i) =
        ∑ k, z (.inl k) * ℓ (algebraMap V (FractionRing V) (s (.inl k))) := by
    intro s hm hu z
    rw [ℓprod _ _ _ (fun i => zpow_ne_zero _ (hs0 s hm hu i)), Fintype.sum_sum_type]
    simp only [ℓzpow, hunit _ (hu _), mul_zero, Finset.sum_const_zero, add_zero]
  let c₁ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))).toNat
  let c₂ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))).toNat
  have hc₁ : ∀ k, (c₁ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₁ (.inl k))) := fun k => by
    have := hneg _ (h1m k).1 (h1m k).2
    simp only [c₁]; omega
  have hc₂ : ∀ k, (c₂ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₂ (.inl k))) := fun k => by
    have := hneg _ (h2m k).1 (h2m k).2
    simp only [c₂]; omega
  refine ⟨c₁, c₂, fun k => ?_, fun k => ?_, ?_⟩
  · have := hc₁ k; have := hneg _ (h1m k).1 (h1m k).2; omega
  · have := hc₂ k; have := hneg _ (h2m k).1 (h2m k).2; omega
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨u, hu⟩ := hprod a b
  have key := congrArg ℓ hu
  rw [ℓmul _ _ (hne _ u.ne_zero) (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs0 s₁ h1m h1u i)),
    hunit _ u.isUnit, zero_add, hsum s₂ h2m h2u, hsum s₁ h1m h1u] at key
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul]
  beta_reduce at key
  have key' : (n:ℤ) * ∑ k, ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = (n:ℤ) * ∑ k, ((c₁ k:ℤ) * ε (.inl k) a b) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = -((n:ℤ) * ε (.inl k) (ga a) (ga b) * ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))) by rw [hc₂]; ring),
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₁ k : ℤ) * ε (.inl k) a b) = -((n:ℤ) * ε (.inl k) a b * ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))) by rw [hc₁]; ring),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, key]
  have := (mul_left_cancel₀ hn' key').symm
  exact this

end GlobalTheory.TInj
