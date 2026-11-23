import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

section RationalValues

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem le_iff_of_pow_eq_zpow {t a b : Γ} (h0 : 0 < t) (h1 : t < 1) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {m m' : ℤ} (ha : a ^ n = t ^ m) (hb : b ^ n' = t ^ m') :
    b ≤ a ↔ (m : ℚ) / n ≤ (m' : ℚ) / n' := by
  have e1 : a ^ (n * n') = t ^ (m * n') := by rw [pow_mul, ha, zpow_mul, zpow_natCast]
  have e2 : b ^ (n * n') = t ^ (m' * n) := by rw [mul_comm n, pow_mul, hb, zpow_mul, zpow_natCast]
  rw [← pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_pos hn hn').ne', e1, e2,
    zpow_le_zpow_iff_right_of_lt_one₀ h0 h1, div_le_div_iff₀ (by exact_mod_cast hn)
      (by exact_mod_cast hn')]
  norm_cast

theorem exists_ratAddValuation_of_pow_eq_zpow {F : Type*} [Field F] (w : Valuation F Γ) {t : Γ}
    (h0 : 0 < t) (h1 : t < 1) (h : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = t ^ m) :
    ∃ v : AddValuation F (WithTop ℚ), ∀ (x : F) (m : ℤ), w x = t ^ m →
      v x = ((m : ℚ) : WithTop ℚ) := by
  classical
  choose! n m hn hnm using h
  let f : F → WithTop ℚ := fun x => if x = 0 then ⊤ else (((m x : ℚ) / n x : ℚ) : WithTop ℚ)
  have f0 : f 0 = ⊤ := if_pos rfl
  have key : ∀ (x : F) (a : ℕ) (b : ℤ), 0 < a → w x ^ a = t ^ b →
      f x = (((b : ℚ) / a : ℚ) : WithTop ℚ) := by
    intro x a b ha hab
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow ha.ne'] at hab
      exact (zpow_pos h0 b).ne hab
    simp only [f, if_neg hx, WithTop.coe_inj]
    exact le_antisymm ((le_iff_of_pow_eq_zpow h0 h1 (hn x hx) ha (hnm x hx) hab).1 le_rfl)
      ((le_iff_of_pow_eq_zpow h0 h1 ha (hn x hx) hab (hnm x hx)).1 le_rfl)
  have mono : ∀ x y : F, w y ≤ w x → f x ≤ f y := by
    intro x y hxy
    by_cases hy : y = 0
    · rw [hy, f0]; exact le_top
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hxy
      exact hy hxy
    simp only [f, if_neg hx, if_neg hy, WithTop.coe_le_coe]
    exact (le_iff_of_pow_eq_zpow h0 h1 (hn x hx) (hn y hy) (hnm x hx) (hnm y hy)).1 hxy
  refine ⟨AddValuation.of f f0 ?_ ?_ ?_, fun x b hb => ?_⟩
  · rw [key 1 1 0 one_pos (by simp)]
    simp
  · intro x y
    rcases le_max_iff.1 (w.map_add x y) with h | h
    · exact min_le_of_left_le (mono _ _ h)
    · exact min_le_of_right_le (mono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, MulZeroClass.zero_mul, f0, top_add]
    by_cases hy : y = 0
    · rw [hy, MulZeroClass.mul_zero, f0, add_top]
    have hx' := hn x hx
    have hy' := hn y hy
    rw [key (x * y) (n x * n y) (m x * n y + m y * n x) (Nat.mul_pos hx' hy') (by
      rw [map_mul, mul_pow, pow_mul, mul_comm (n x), pow_mul, hnm x hx, hnm y hy,
        zpow_add₀ h0.ne', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])]
    simp only [f, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have : (n x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne'
    have : (n y : ℚ) ≠ 0 := by exact_mod_cast hy'.ne'
    push_cast
    field_simp
  · change f x = _
    rw [key x 1 b one_pos (by simpa using hb)]
    simp

theorem exists_valuation_pow_eq_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Valuation F Γ) {x : F} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hx
  let g : ℕ → F := fun i => algebraMap K F (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, g i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  have hc : ∀ i ∈ p.support, w (algebraMap K F (p.coeff i)) ≠ 0 := fun i hi => by
    simpa using hi
  have hw : w x ≠ 0 := by simpa using hx0
  have aux : ∀ i ∈ p.support, ∀ j ∈ p.support, j < i → w (g i) = w (g j) →
      ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
    intro i hi j hj hji e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hji
    refine ⟨d + 1, p.coeff j / p.coeff (j + d + 1), Nat.succ_pos d,
      div_ne_zero (Polynomial.mem_support_iff.1 hj) (Polynomial.mem_support_iff.1 hi), ?_⟩
    simp only [g, map_mul, map_pow] at e
    rw [map_div₀, map_div₀, eq_div_iff (hc _ hi)]
    apply mul_right_cancel₀ (pow_ne_zero j hw)
    rw [← e, _root_.add_assoc j, pow_add (w x) j]
    ac_rfl
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i => w (g i))
    (Polynomial.support_nonempty.2 hp0)
  by_contra hne
  have hlt : ∀ j ∈ p.support \ {i}, w (g j) < w (g i) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    refine lt_of_le_of_ne (hmax j hj.1) fun e => hne ?_
    rcases lt_or_gt_of_ne hj.2 with h | h
    · exact aux i hi j hj.1 h e.symm
    · exact aux j hj.1 i hi h e
  have hgi : w (g i) ≠ 0 := by
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hc i hi) (pow_ne_zero i hw)
  have := w.map_sum_eq_of_lt hi hlt
  rw [hsum, map_zero] at this
  exact hgi this.symm

end RationalValues

theorem exists_valOver_of_isAlgebraic {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] :
    ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  let K := FractionRing V
  let f : V →+* F := (algebraMap K F).comp (algebraMap V K)
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective V K)
  obtain ⟨W, hW⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hW1, hW2⟩ := (localSubring_range_le_valuationSubring_iff f W).1 hW
  let w := W.valuation
  have h0 : 0 < w (f ϖ) := by
    rw [Valuation.pos_iff]
    exact (map_ne_zero_iff _ hf).2 hϖ.ne_zero
  have h1 : w (f ϖ) < 1 := (W.mem_nonunits_iff).1 (hW2 ϖ hϖ.not_isUnit)
  have hu : ∀ u : Vˣ, w (f u) = 1 := fun u =>
    W.valuation_unit (Units.map (f.codRestrict W hW1 : V →* W) u)
  have hval : ∀ (c : K) (n : ℤ), HasVal ϖ c n → w (algebraMap K F c) = w (f ϖ) ^ n := by
    rintro c n ⟨u, rfl⟩
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀]
    change w (f ϖ) ^ n * w (f u) = _
    rw [hu, _root_.mul_one]
  obtain ⟨v, hv⟩ := exists_ratAddValuation_of_pow_eq_zpow w h0 h1 fun x hx => by
    obtain ⟨n, c, hn, hc, e⟩ := exists_valuation_pow_eq_of_isAlgebraic (K := K) w
      (Algebra.IsAlgebraic.isAlgebraic x) hx
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    exact ⟨n, m, hn, e.trans (hval c m hm)⟩
  exact ⟨v, fun c n hc => hv _ n (hval c n hc)⟩

theorem exists_complete_discreteValuationRing_map_le {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V := by
  by_cases h : I = ⊥
  · let K := FractionRing R
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance,
      (PowerSeries.C (R := K)).comp (algebraMap R K), ?_,
      PowerSeries.C_injective.comp (IsFractionRing.injective R K), by simp [h]⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  · obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    have := hp.isPrime
    obtain ⟨O, _, _, _, hO, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt
      (⊥ : Ideal R) p (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 h) hIp)
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, hO,
      (RingHom.injective_iff_ker_eq_bot φ).2 h1, Ideal.map_le_iff_le_comap.2 (h2 ▸ hIp)⟩

theorem adic_base_embeds_valuation_algebraic_closure :
    (∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v := by
  refine ⟨fun R _ _ _ I hR => ?_, fun V _ _ _ ϖ hϖ => exists_valOver_of_isAlgebraic hϖ _⟩
  obtain ⟨hN, -, -, hc⟩ := hR
  refine exists_complete_discreteValuationRing_map_le ?_
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton hc.toIsHausdorff)

end GlobalTheory
