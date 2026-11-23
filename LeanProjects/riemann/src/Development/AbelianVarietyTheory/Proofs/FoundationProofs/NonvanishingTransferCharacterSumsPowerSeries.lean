import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombinationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDiracStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AmiceRiemannSumCongrDiracCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePowStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem exists_series_limit : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (b : ℕ → ℕ → Qbar l) (t : ℕ → ℕ → ℕ), (∀ N j, b N j ∈ c.O) → ∃ A : PowerSeries (Qbar l), (∀ n, A.coeff n ∈ c.O) ∧ ∀ (g z X : Qbar l) (M N₀ : ℕ) (δ : ℝ), ‖z - 1‖ ≤ 1 → ‖g‖ * ‖z - 1‖ ^ M ≤ δ → (∀ N, N₀ ≤ N → ‖g * ∑ j ∈ Finset.range N, b N j * z ^ (t N j) - X‖ ≤ δ) → ‖g * tval A M z - X‖ ≤ δ := by
  intro l _ c b t hb
  let a : ℕ → ℕ → Qbar l := fun n N => ∑ j ∈ Finset.range N, b N j * ((t N j).choose n : Qbar l)
  have ha : ∀ n N, a n N ∈ c.O := fun n N => sum_mem fun j _ => mul_mem (hb N j) (natCast_mem _ _)
  have hlim : ∀ n, ∃ y ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds y) := by
    intro n
    obtain ⟨y, hy, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨y, hy, h⟩
  choose y hy hay using hlim
  refine ⟨PowerSeries.mk y, fun n => by simpa using hy n, fun g z X M N₀ δ hz hδ hN => ?_⟩
  unfold tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun N => ‖g * ∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - X‖) (Filter.hyperfilter ℕ)
      (nhds ‖g * ∑ n ∈ Finset.range M, y n * (z - 1) ^ n - X‖) :=
    (((tendsto_finset_sum _ fun n _ => (hay n).mul_const _).const_mul _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ N in (Filter.hyperfilter ℕ : Filter ℕ), N₀ ≤ N :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop N₀)
  filter_upwards [hev] with N hN'
  rw [show g * ∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - X =
    g * (∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - ∑ j ∈ Finset.range N, b N j * z ^ (t N j)) +
      (g * ∑ j ∈ Finset.range N, b N j * z ^ (t N j) - X) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_trans ?_ hδ) (hN N hN'))
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hb N j))).trans ?_
  have h := GlobalTheory.AmiceDist.norm_trunc_binomial hz M (t N j)
  rwa [sub_add_cancel] at h

theorem exists_coef_roots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l), ‖x‖ ≤ 1 → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O ∧ ∀ y : Qbar l, y ^ (l - 1) = 1 → y ∈ c'.O := by
  intro l _ c x hx
  have h1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  haveI : NeZero (l - 1) := ⟨h1.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Qbar l, IsPrimitiveRoot ζ (l - 1) := HasEnoughRootsOfUnity.prim
  obtain ⟨c₁, h₁, hx₁⟩ := (UpperTheory.V.HV.coefSup l).2.2.1 c x (GlobalTheory.BlochKatoIntegralScalars.isIntegral_of_norm_le_one x hx)
  obtain ⟨c₂, h₂, hx₂⟩ := (UpperTheory.V.HV.coefSup l).2.2.1 c₁ ζ (hζ.isIntegral h1).tower_top
  refine ⟨c₂, h₁.trans h₂, h₂ hx₁, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  exact pow_mem hx₂ i

theorem lower_bound_of_not_cg : ∀ (l : ℕ) [Fact l.Prime] (f : Qbar l) (S T : ℕ → Qbar l) (n₀ r₁ : ℕ), f ≠ 0 → (∀ r, r₁ ≤ r → Cg (2 * r) (f * S r) ((l : Qbar l) ^ r * T r)) → (∀ r, r₁ ≤ r → ¬ Cg (n₀ + r) (S r) 0) → ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℕ, ∀ r, R ≤ r → δ < ‖T r‖ := by
  intro l _ f S T n₀ r₁ hf h1 h2
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  have hδ : 0 < ‖f‖ * ‖(l : Qbar l)‖ ^ n₀ := mul_pos (norm_pos_iff.2 hf) (pow_pos hq0 _)
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨_, hδ, max R r₁, fun r hr => ?_⟩
  by_contra hT
  rw [not_lt] at hT
  have a1 := h1 r (le_of_max_le_right hr)
  have a2 := h2 r (le_of_max_le_right hr)
  unfold Cg at a1 a2
  rw [sub_zero] at a2
  apply a2
  have hr' : ‖(l : Qbar l)‖ ^ r ≤ ‖f‖ * ‖(l : Qbar l)‖ ^ n₀ :=
    (pow_le_pow_of_le_one hq0.le hq1.le (le_of_max_le_left hr)).trans hR.le
  have a3 : ‖f * S r‖ ≤ ‖(l : Qbar l)‖ ^ r * (‖f‖ * ‖(l : Qbar l)‖ ^ n₀) := by
    rw [show f * S r = (f * S r - (l : Qbar l) ^ r * T r) + (l : Qbar l) ^ r * T r by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (a1.trans ?_) ?_)
    · rw [norm_pow, two_mul, pow_add]; gcongr
    · rw [norm_mul, norm_pow]; gcongr
  rw [norm_mul] at a3
  refine le_of_mul_le_mul_left (a3.trans_eq ?_) (norm_pos_iff.2 hf)
  rw [norm_pow, pow_add]; ring

theorem not_cg_of_lower_bound : ∀ (l : ℕ) [Fact l.Prime] (δ : ℝ), 0 < δ → ∃ n₁ : ℕ, ∀ r, n₁ ≤ r → ∀ S T : Qbar l, δ < ‖T‖ → Cg (2 * r) S ((l : Qbar l) ^ r * T) → ¬ Cg (n₁ + r) S 0 := by
  intro l _ δ hδ
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨n, fun r hr S T hT h1 h2 => ?_⟩
  unfold Cg at h1 h2
  rw [sub_zero] at h2
  have a3 : ‖(l : Qbar l) ^ r * T‖ ≤ ‖(l : Qbar l)‖ ^ r * ‖(l : Qbar l)‖ ^ n := by
    rw [show (l : Qbar l) ^ r * T = -(S - (l : Qbar l) ^ r * T) + S by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h2.trans_eq ?_))
    · rw [norm_neg]
      refine h1.trans ?_
      rw [norm_pow, ← pow_add]
      exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    · rw [norm_pow, pow_add, mul_comm]
  rw [norm_mul, norm_pow] at a3
  have := le_of_mul_le_mul_left a3 (pow_pos hq0 r)
  linarith

theorem norm_tval_le_of_coeff_cg : ∀ (l : ℕ) [Fact l.Prime] (A B : PowerSeries (Qbar l)) (w : ℕ → Qbar l) (z : Qbar l) (M : ℕ), (∀ m, ‖w m‖ = 1) → ‖z - 1‖ ≤ 1 → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n)) → ‖tval B M z‖ ≤ ‖tval A M z‖ := by
  intro l _ A B w z M hw hz h
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq1
  obtain ⟨m, hm⟩ := h k
  have a1 : ‖tval A M z - w m * tval B M z‖ ≤ ‖(l : Qbar l) ^ k‖ := by
    unfold tval
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n _ => ?_
    rw [← mul_assoc, ← sub_mul, norm_mul, norm_pow (z - 1)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans (hm m le_rfl n)
  have a2 := norm_sub_norm_le (w m * tval B M z) (tval A M z)
  rw [norm_mul, hw, one_mul, norm_sub_rev] at a2
  rw [norm_pow] at a1
  linarith

theorem cg_div_gauss : ∀ (l : ℕ) [Fact l.Prime] (k c₁ : ℕ) (SG SL τ τ' TG TL f v v' a a' κ p : Qbar l), 2 * c₁ ≤ k → ‖v‖ = 1 → ‖v'‖ = 1 → ‖a‖ = 1 → ‖a'‖ = 1 → ‖p‖ ≤ 1 → ‖p * κ‖ ≤ 1 → τ * τ' = (l : Qbar l) ^ (k + 1) → ‖τ'‖ ≤ ‖(l : Qbar l) ^ ((k + 1) / 2)‖ → Cg (k + 1) SG (τ * TG) → Cg (k + 1) (f * SL) (τ * TL) → Cg (k + 1 - c₁) (f * (v' * κ * a' ^ (k + 1) * SL)) (v * a ^ (k + 1) * SG) → Cg (k / 2 - c₁) (p * TG) (v' / v * (a' / a) * (a' / a) ^ k * (p * κ * TL)) := by
  intro l _ k c₁ SG SL τ τ' TG TL f v v' a a' κ p hk hv hv' ha ha' hp hpκ hτ hτ' h1 h2 h3
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := (GlobalTheory.KZ.norm_prime_lt_one_qbar l).le
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  unfold Cg at h1 h2 h3 ⊢
  rw [norm_pow] at h1 h2 h3 hτ' ⊢
  set D := p * TG - v' / v * (a' / a) * (a' / a) ^ k * (p * κ * TL) with hD
  have hm : ‖(l : Qbar l)‖ ^ (k + 1) ≤ ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := pow_le_pow_of_le_one hq0.le hq1 (by omega)
  have e : v * a ^ (k + 1) * (τ * D) = (-(p * (v * a ^ (k + 1) * (SG - τ * TG))) +
      -(p * (f * (v' * κ * a' ^ (k + 1) * SL) - v * a ^ (k + 1) * SG))) + p * κ * (v' * a' ^ (k + 1) * (f * SL - τ * TL)) := by
    rw [hD, div_pow]; field_simp; ring
  have b1 : ‖τ‖ * ‖D‖ ≤ ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := by
    have : ‖τ‖ * ‖D‖ = ‖v * a ^ (k + 1) * (τ * D)‖ := by simp [hv, ha]
    rw [this, e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
    · rw [norm_neg, norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hp).trans ?_
      rw [norm_mul, norm_mul, norm_pow, hv, ha, one_pow, one_mul, one_mul]
      exact h1.trans hm
    · rw [norm_neg, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans h3
    · rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hpκ).trans ?_
      rw [norm_mul, norm_mul, norm_pow, hv', ha', one_pow, one_mul, one_mul]
      exact h2.trans hm
  have b2 : ‖(l : Qbar l)‖ ^ (k + 1) * ‖D‖ ≤ ‖(l : Qbar l)‖ ^ ((k + 1) / 2) * ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := by
    rw [← norm_pow, ← hτ, norm_mul, mul_comm ‖τ‖, mul_assoc]
    gcongr
  refine le_of_mul_le_mul_left (b2.trans ?_) (pow_pos hq0 (k + 1))
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_of_le_one hq0.le hq1 (by omega)

theorem ratio_units_cg : ∀ (l : ℕ) [Fact l.Prime] (v v' : ℕ → Qbar l) (u : Qbar l), ‖u‖ = 1 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → ∀ k, ‖v' (k + 1) / v (k + 1) * u‖ = 1 ∧ Cg k (v' (k + 1 + 1) / v (k + 1 + 1) * u) (v' (k + 1) / v (k + 1) * u) := by
  intro l _ v v' u hu hv hv' k
  have hq1 := (GlobalTheory.KZ.norm_prime_lt_one_qbar l).le
  have hv0 : ∀ m, v m ≠ 0 := fun m h => by have := (hv m).1; rw [h] at this; simp at this
  refine ⟨by rw [norm_mul, norm_div, (hv _).1, (hv' _).1, hu]; simp, ?_⟩
  have a1 := (hv (k + 1)).2
  have a2 := (hv' (k + 1)).2
  unfold Cg at a1 a2 ⊢
  have e : v' (k + 1 + 1) / v (k + 1 + 1) * u - v' (k + 1) / v (k + 1) * u =
      u / (v (k + 1 + 1) * v (k + 1)) * (v (k + 1) * (v' (k + 1 + 1) - v' (k + 1)) + -(v' (k + 1) * (v (k + 1 + 1) - v (k + 1)))) := by
    have := hv0 (k + 1); have := hv0 (k + 1 + 1)
    field_simp; ring
  rw [e, norm_mul, norm_div, norm_mul, (hv _).1, (hv _).1, hu, mul_one, div_one, one_mul]
  refine le_trans ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) (b := ‖(l : Qbar l) ^ (k + 1)‖) ?_
  · rwa [norm_mul, (hv _).1, one_mul]
  · rwa [norm_neg, norm_mul, (hv' _).1, one_mul]
  · rw [norm_pow, norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hq1 (by omega)

theorem smoothing_factor_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (c₀ e : ℕ), 2 ≤ c₀ → ¬ l ∣ c₀ → 1 - (c₀ : Qbar l) * ((c₀ : Qbar l) ^ e * φ (c₀ : ZMod l)) ≠ 0 := by
  intro l _ φ c₀ e h2 hl h
  have hlp := (Fact.out : l.Prime)
  have h0 : (c₀ : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h1 : φ (c₀ : ZMod l) ^ (l - 1) = 1 := by rw [← map_pow, ZMod.pow_card_sub_one_eq_one h0, map_one]
  have h3 : ((c₀ : Qbar l) * ((c₀ : Qbar l) ^ e * φ (c₀ : ZMod l))) ^ (l - 1) = 1 := by rw [← sub_eq_zero.1 h, one_pow]
  rw [← mul_assoc, mul_pow, h1, mul_one, ← pow_succ', ← pow_mul] at h3
  have h4 : c₀ ^ ((e + 1) * (l - 1)) = 1 := by exact_mod_cast h3
  have h5 : (e + 1) * (l - 1) ≠ 0 := mul_ne_zero (by omega) (by have := hlp.two_le; omega)
  have := (Nat.pow_eq_one.1 h4).resolve_right h5
  omega

theorem norm_char_le_one : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (ψ : DirichletCharacter (Qbar l) n) (x : ZMod n), 0 < n → ‖ψ x‖ ≤ 1 := by
  intro l _ n ψ x _
  exact ψ.norm_le_one x

theorem mellin_comp (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l)
    (e d : ℕ) (hl2 : l ≠ 2) (hc : ∀ y : Qbar l, y ^ (l - 1) = 1 → y ∈ c.O) (hF : ∀ n, F.coeff n ∈ c.O) :
    ∃ A : PowerSeries (Qbar l), (∀ n, A.coeff n ∈ c.O) ∧
      (∀ r, 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
        Cg (2 * r) ((d : Qbar l) ^ e * φ (d : ZMod l) * rSum φ e F r ξ) ((l : Qbar l) ^ r * tval A r ((1 + (l : Qbar l)) ^ e))) ∧
      ∀ k, 1 ≤ k → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ (k + 1)) → ∀ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)),
        ψ.IsPrimitive → InComp φ e ψ → ∀ ζ : Qbar l, ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ → ζ ^ (l ^ k) = 1 →
        Cg (k + 1) (ψ⁻¹ (d : ZMod (l ^ (k + 1))) * chSum F (k + 1) z ψ) (gSum (k + 1) z ψ * tval A (l ^ (3 * k)) ζ) := by
  have hlp := (Fact.out : l.Prime)
  have hl1 : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hmono : ∀ {i j : ℕ}, i ≤ j → ‖(l : Qbar l) ^ j‖ ≤ ‖(l : Qbar l) ^ i‖ := fun h => by
    rw [norm_pow, norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1 h
  choose a haO ha using fun N => GlobalTheory.T.truncated_shifted_series_eq_integral_poly_combination l c F N hF
  choose ε t hε hεr hεc using fun R j => GlobalTheory.T.teichmuller_decomposition_dirichlet_twisted_power l φ e R j hl2
  have hεO : ∀ R j, ε R j ∈ c.O := fun R j => (hε R j).elim (fun h => h ▸ zero_mem _) (hc _)
  have hF1 : ∀ n, ‖F.coeff n‖ ≤ 1 := fun n => FirstDer.norm_le_one_of_mem c (hF n)
  have ha1 : ∀ N j, ‖a N j‖ ≤ 1 := fun N j => FirstDer.norm_le_one_of_mem c (haO N j)
  obtain ⟨A, hAO, hA⟩ := exists_series_limit l c (fun N j => a N j * ε N (d * j)) (fun N j => t N (d * j))
    (fun N j => mul_mem (haO N j) (hεO _ _))
  refine ⟨A, hAO, fun r hr ξ hξ => ?_, fun k hk z hz ψ hψ hin ζ hζ hζ1 => ?_⟩
  · have hy : ‖(1 + (l : Qbar l)) ^ e - 1‖ ≤ ‖(l : Qbar l)‖ := by
      rw [← mul_geom_sum, add_sub_cancel_left, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      have : ∑ i ∈ Finset.range e, (1 + (l : Qbar l)) ^ i = ((∑ i ∈ Finset.range e, (1 + l) ^ i : ℕ) : Qbar l) := by
        push_cast; rfl
      rw [this]; exact IsUltrametricDist.norm_natCast_le_one _ _
    unfold Cg
    rw [norm_sub_rev]
    refine hA _ _ _ r (l ^ (3 * r) + r) _ (hy.trans hl1) ?_ fun N hN => ?_
    · rw [two_mul, pow_add, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_pow (l : Qbar l)]
      exact pow_le_pow_left₀ (norm_nonneg _) hy r
    · have h1 := GlobalTheory.T.amiceRiemannSum_congr_dirac_coefficients l φ e F (a N) N r ξ hr (by omega) hF1 (ha1 N) (ha N) hξ
      unfold Cg at h1
      have e1 : (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)) -
          (d : Qbar l) ^ e * φ (d : ZMod l) * rSum φ e F r ξ =
          -((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * (φ ((d * j : ℕ) : ZMod l) * ((d * j : ℕ) : Qbar l) ^ e -
            ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)))) +
          -((d : Qbar l) ^ e * φ (d : ZMod l) * (rSum φ e F r ξ -
            (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * (φ (j : ZMod l) * (j : Qbar l) ^ e))) := by
        have e2 : ∑ j ∈ Finset.range N, a N j * (φ ((d * j : ℕ) : ZMod l) * ((d * j : ℕ) : Qbar l) ^ e -
            ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j))) =
            (d : Qbar l) ^ e * φ (d : ZMod l) * ∑ j ∈ Finset.range N, a N j * (φ (j : ZMod l) * (j : Qbar l) ^ e) -
            ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.cast_mul, Nat.cast_mul, map_mul]; ring
        rw [e2]; ring
      rw [e1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_neg, norm_mul, two_mul, pow_add, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha1 N j)).trans ((hεr N (d * j)).trans (hmono (by omega)))
      · rw [norm_neg, norm_mul]
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans h1
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ d)) (norm_nonneg _)
          (norm_char_le_one l l φ _ hlp.pos)
  · have hg : ‖gSum (k + 1) z ψ‖ ≤ 1 := (GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power l (k + 1) z ψ hz.pow_eq_one).trans (by simpa using hmono (Nat.zero_le _))
    unfold Cg
    rw [norm_sub_rev]
    refine hA _ _ _ (l ^ (3 * k)) (l ^ (3 * (k + 1)) + (k + 1)) _ (GlobalTheory.AmiceDist.norm_sub_one_le hζ1) ?_ fun N hN => ?_
    · exact (mul_le_of_le_one_left (by positivity) hg).trans
        ((GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hζ1).trans (hmono (by omega)))
    · have h1 := GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac l F (a N) N (k + 1) z ψ (by omega) (by omega) hF1 (ha N) hz hψ
      unfold Cg at h1
      have e2 : ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ζ ^ (t N (d * j)) =
          ψ⁻¹ (d : ZMod (l ^ (k + 1))) * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h2 := hεc N (d * j) (k + 1) (by omega) (by omega) ψ hin
        rw [Nat.cast_mul, map_mul, hζ] at h2
        rw [mul_assoc, ← h2]; ring
      have e1 : gSum (k + 1) z ψ * (ψ⁻¹ (d : ZMod (l ^ (k + 1))) * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1)))) -
          ψ⁻¹ (d : ZMod (l ^ (k + 1))) * chSum F (k + 1) z ψ = -(ψ⁻¹ (d : ZMod (l ^ (k + 1))) * (chSum F (k + 1) z ψ -
            gSum (k + 1) z ψ * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1))))) := by ring
      rw [e2, e1, norm_neg, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one l _ ψ⁻¹ _ (pow_pos hlp.pos _))).trans (h1.trans (hmono (by omega)))

theorem nonvanishing_transfer : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0 := by
  intro l _ c Gs L a a' κ v v' c₀ m₀ c₁ n₀ φ e hl2 he hm₀ hGs hL ha ha' hκ hv hv' hc₀ hlc₀ hyp hLnz
  obtain ⟨r₁, hr₁⟩ := hLnz
  have hlp := (Fact.out : l.Prime)
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hc1 : ‖(c₀ : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ c₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(l : Qbar l) ^ N * κ‖ ≤ 1 := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hκ)) (GlobalTheory.KZ.norm_prime_lt_one_qbar l)
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_pow, ← le_div_iff₀ (norm_pos_iff.2 hκ), one_div]
    exact hN.le
  set p : Qbar l := (l : Qbar l) ^ N with hp
  have hp0 : p ≠ 0 := pow_ne_zero _ hl0
  have hp1 : ‖p‖ ≤ 1 := by
    rw [hp, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ l)
  obtain ⟨c', hcc, hκO, hroot⟩ := exists_coef_roots l c _ hN
  obtain ⟨AG, hGO, hGr, hGc⟩ := mellin_comp l c' Gs φ e 1 hl2 hroot fun n => hcc (hGs n)
  obtain ⟨A₁, h1O, h1r, h1c⟩ := mellin_comp l c' L φ e 1 hl2 hroot fun n => hcc (hL n)
  obtain ⟨A₂, h2O, h2r, h2c⟩ := mellin_comp l c' L φ e c₀ hl2 hroot fun n => hcc (hL n)
  simp only [Nat.cast_one, one_pow, map_one, one_mul] at hGr hGc h1r h1c
  have hcomb : ∀ (n : ℕ) (x₁ y₁ x₂ y₂ : Qbar l), Cg n x₁ y₁ → Cg n x₂ y₂ → Cg n (x₁ - (c₀ : Qbar l) * x₂) (y₁ - (c₀ : Qbar l) * y₂) := by
    intro n x₁ y₁ x₂ y₂ h1 h2
    unfold Cg at h1 h2 ⊢
    rw [show x₁ - (c₀ : Qbar l) * x₂ - (y₁ - (c₀ : Qbar l) * y₂) = (x₁ - y₁) + -((c₀ : Qbar l) * (x₂ - y₂)) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans h2
  set AL := A₁ - PowerSeries.C (c₀ : Qbar l) * A₂ with hAL
  have hprim : ∀ r : ℕ, ∃ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) := fun r =>
    haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    HasEnoughRootsOfUnity.prim
  choose ξ hξ using hprim
  obtain ⟨δ, hδ, R, hR⟩ := lower_bound_of_not_cg l _ (fun r => rSum φ e L r (ξ r)) (fun r => tval AL r ((1 + (l : Qbar l)) ^ e)) n₀ (max r₁ 1)
    (smoothing_factor_ne_zero l φ c₀ e hc₀ hlc₀)
    (fun r hr => by
      have h := hcomb _ _ _ _ _ (h1r r (le_of_max_le_right hr) _ (hξ r)) (h2r r (le_of_max_le_right hr) _ (hξ r))
      rw [hAL, tval_sub_C_mul]
      convert h using 1 <;> ring)
    (fun r hr => hr₁ r (le_of_max_le_left hr) (le_of_max_le_right hr) _ (hξ r))
  have hu : ‖a' / a‖ = 1 := by rw [norm_div, ha, ha', div_one]
  have hw := ratio_units_cg l v v' (a' / a) hu hv hv'
  have hBO : ∀ n, (PowerSeries.C (p * κ) * AL).coeff n ∈ c'.O := fun n => by
    rw [PowerSeries.coeff_C_mul, hAL, map_sub, PowerSeries.coeff_C_mul]
    exact mul_mem hκO (sub_mem (h1O n) (mul_mem (natCast_mem _ _) (h2O n)))
  have hAO : ∀ n, (PowerSeries.C p * AG).coeff n ∈ c'.O := fun n => by
    rw [PowerSeries.coeff_C_mul]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (hGO n)
  have hpκ : 0 < ‖p * κ‖ := norm_pos_iff.2 (mul_ne_zero hp0 hκ)
  have hB0 : PowerSeries.C (p * κ) * AL ≠ 0 := by
    intro h0
    have h1 := tval_C_mul AL (p * κ) R ((1 + (l : Qbar l)) ^ e)
    rw [h0] at h1
    have h2 : tval (0 : PowerSeries (Qbar l)) R ((1 + (l : Qbar l)) ^ e) = 0 := by simp [tval]
    rw [h2] at h1
    have h3 := (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp0 hκ)
    have h4 := hR R le_rfl
    simp only [h3, norm_zero] at h4
    linarith
  obtain ⟨-, hpin⟩ := GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots l c' _ _ (a' / a) (fun k => v' (k + 1) / v (k + 1) * (a' / a)) c₁ (m₀ + 2 * c₁) hAO hBO hB0 hu hw
    (fun k hk ζ hζ => by
      obtain ⟨z, hz, hzψ⟩ := hyp (k + 1) (by omega)
      obtain ⟨ψ, hψ, hin, hψζ⟩ := GlobalTheory.T.exists_primitive_character_twist l φ e k ζ hl2 (by omega) hζ
      have g1 := hGc k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one
      have g2 := hcomb _ _ _ _ _ (h1c k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one)
        (h2c k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one)
      rw [tval_C_mul, tval_C_mul]
      refine cg_div_gauss l k c₁ (chSum Gs (k + 1) z ψ) (chSum L (k + 1) z ψ) _ _ _ _
        (1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ (k + 1)))) _ _ a a' κ p (by omega) (hv _).1 (hv' _).1 ha ha' hp1 hN
        (GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow l (k + 1) z ψ hz hψ) (GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power l (k + 1) z⁻¹ ψ⁻¹ hz.inv.pow_eq_one) g1 ?_ (hzψ ψ hψ)
      rw [hAL, tval_sub_C_mul]
      convert g2 using 1 <;> ring)
  have hy : ‖(1 + (l : Qbar l)) ^ e - 1‖ ≤ 1 := by
    have : (1 + (l : Qbar l)) ^ e - 1 = (((1 + l) ^ e - 1 : ℤ) : Qbar l) := by push_cast; rfl
    rw [this]; exact IsUltrametricDist.norm_intCast_le_one _ _
  obtain ⟨n₁, hn₁⟩ := not_cg_of_lower_bound l (‖p * κ‖ * δ) (mul_pos hpκ hδ)
  refine ⟨n₁, max (max n₁ R) 1, fun r hr η hη => hn₁ r (by omega) _ _ ?_ (hGr r (by omega) η hη)⟩
  have h := norm_tval_le_of_coeff_cg l _ _ _ _ r (fun m => (hw m).1) hy hpin
  rw [tval_C_mul, tval_C_mul, norm_mul, norm_mul p (tval _ _ _)] at h
  exact ((mul_lt_mul_of_pos_left (hR r (by omega)) hpκ).trans_le h).trans_le (mul_le_of_le_one_left (norm_nonneg _) hp1)

end GlobalTheory.KZ.Cmp
