import Formalism.EisensteinCokernelLengths.RationalTailBound
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.GaussRam
import Formalism.GaussValuationBounds.NokLemmaCVal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

open scoped ENNReal
open Formalism.NOK

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cvr_gaussV_letter {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : 1 ≤ e) {x : ℝ} (hx : 0 < x)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (E : Polynomial O) (u : PowerSeries O) (s : ℕ)
    (hEis : EisE ϖ e E (ℓ ^ s)) (hu : IsUnit u) :
    gaussV x (u * (E : PowerSeries O)) = ENNReal.ofReal (min (e : ℝ) (x * (ℓ : ℝ) ^ s)) := by
  have hN : 1 ≤ ℓ ^ s := Nat.one_le_pow _ _ hℓ
  rw [gaussValMul O x hx, gaussValUnit O x hx.le u hu, zero_add,
    gaussValEisenstein O ϖ hϖ e he x hx.le E (ℓ ^ s) hN hEis, Nat.cast_pow]

private theorem gaussV_pow {x : ℝ} (hx : 0 < x) (f : PowerSeries O) (n : ℕ) :
    gaussV x (f ^ n) = n * gaussV x f := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact gaussValUnit O x hx.le 1 isUnit_one
  | succ n ih => rw [pow_succ, gaussValMul O x hx, ih, Nat.cast_succ, add_mul, one_mul]

private theorem gaussV_prod_range {x : ℝ} (hx : 0 < x) (f : ℕ → PowerSeries O) (n : ℕ) :
    gaussV x (∏ s ∈ Finset.range n, f s) = ∑ s ∈ Finset.range n, gaussV x (f s) := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_zero]
    exact gaussValUnit O x hx.le 1 isUnit_one
  | succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, gaussValMul O x hx, ih]

private theorem gaussV_C_pow_irreducible {ϖ : O} (hϖ : Irreducible ϖ) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    gaussV x (PowerSeries.C (ϖ ^ n)) = n := by
  rw [gaussValC O x hx, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  simp

theorem cvr_step {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : 1 ≤ e) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O)
    (hEis : ∀ s, EisE ϖ e (E s) (ℓ ^ s))
    (hu : ∀ s, IsUnit (u s)) {ell g a b₀ b₁ s₀ s₁ k : ℕ} (hs : s₀ < s₁)
    (hmem : PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
      Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁})
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ e)
    (hlt : (a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ < b₁ * τ) :
    (k : ℝ) ≤ (a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓ0 : (0:ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hpow1 : (0:ℝ) < (ℓ:ℝ) ^ s₁ := pow_pos hℓ0 _
  have hpne : (ℓ:ℝ) ^ s₁ ≠ 0 := hpow1.ne'
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = τ / (ℓ:ℝ) ^ s₁ := ⟨_, rfl⟩
  have hx : 0 < x := by rw [hxdef]; exact div_pos hτ0 hpow1
  have hxl : x * (ℓ:ℝ) ^ s₁ = τ := by rw [hxdef]; field_simp
  have key : (ℓ:ℝ) ^ s₀ * ℓ ≤ (ℓ:ℝ) ^ s₁ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by exact_mod_cast hℓ1) hs
  have hM := gaussValMul O x hx
  have hF : ∀ s, gaussV x (u s * (E s : PowerSeries O)) ≤ (e : ℝ≥0∞) := by
    intro s
    rw [cvr_gaussV_letter hϖ he hx hℓ1 (E s) (u s) s (hEis s) (hu s), ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hF1 : gaussV x (u s₁ * (E s₁ : PowerSeries O)) = ENNReal.ofReal τ := by
    rw [cvr_gaussV_letter hϖ he hx hℓ1 (E s₁) (u s₁) s₁ (hEis s₁) (hu s₁), hxl, min_eq_right hτ1]
  have hF0 : gaussV x (u s₀ * (E s₀ : PowerSeries O)) ≤ ENNReal.ofReal (τ / ℓ) := by
    rw [cvr_gaussV_letter hϖ he hx hℓ1 (E s₀) (u s₀) s₀ (hEis s₀) (hu s₀)]
    apply ENNReal.ofReal_le_ofReal
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hℓ0, ← hxl, mul_assoc]
    exact mul_le_mul_of_nonneg_left key hx.le
  have hval : gaussV x (PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀) =
      (a : ℝ≥0∞) + 2 * ∑ s ∈ Finset.range ell, (g : ℝ≥0∞) * gaussV x (u s * (E s : PowerSeries O)) +
        b₀ * gaussV x (u s₀ * (E s₀ : PowerSeries O)) := by
    rw [hM (PowerSeries.C (ϖ ^ a) * (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2),
      hM (PowerSeries.C (ϖ ^ a)), gaussV_C_pow_irreducible hϖ hx.le]
    simp only [gaussV_pow hx, gaussV_prod_range hx, Nat.cast_ofNat]
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hmem
  have hlow := minLeGaussValAdd O x (c * PowerSeries.C (ϖ ^ k))
    (d * (u s₁ * (E s₁ : PowerSeries O)) ^ b₁)
  rw [hcd, hval] at hlow
  have hA : (k : ℝ≥0∞) ≤ gaussV x (c * PowerSeries.C (ϖ ^ k)) := by
    rw [hM, gaussV_C_pow_irreducible hϖ hx.le]; exact le_add_self
  have hB : ENNReal.ofReal (b₁ * τ) ≤ gaussV x (d * (u s₁ * (E s₁ : PowerSeries O)) ^ b₁) := by
    rw [hM, gaussV_pow hx, hF1, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact le_add_self
  have hτℓ : (0:ℝ) ≤ τ / ℓ := div_nonneg hτ0.le hℓ0.le
  have hup : (a : ℝ≥0∞) + 2 * ∑ s ∈ Finset.range ell, (g : ℝ≥0∞) * gaussV x (u s * (E s : PowerSeries O)) +
        b₀ * gaussV x (u s₀ * (E s₀ : PowerSeries O)) ≤
      ENNReal.ofReal ((a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ) := by
    calc _ ≤ (a : ℝ≥0∞) + 2 * ∑ s ∈ Finset.range ell, (g : ℝ≥0∞) * (e : ℝ≥0∞) +
          b₀ * ENNReal.ofReal (τ / ℓ) := by
          gcongr with s _
          all_goals first | exact hF s | exact hF0
      _ = ENNReal.ofReal ((a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ) := by
          have h1 : (a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ =
              (a : ℝ) + ((2 * e * g * ell : ℕ) : ℝ) + b₀ * (τ / ℓ) := by push_cast; ring
          rw [h1, ENNReal.ofReal_add (by positivity) (mul_nonneg (Nat.cast_nonneg _) hτℓ),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg _), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp only [ENNReal.ofReal_natCast]
          push_cast
          ring
  have hτℓ' : (0:ℝ) ≤ (b₀:ℝ) / ℓ * τ := mul_nonneg (div_nonneg (Nat.cast_nonneg _) hℓ0.le) hτ0.le
  have hVr : (0:ℝ) ≤ (a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ := by
    have : (0:ℝ) ≤ (a : ℝ) + 2 * e * g * ell := by positivity
    linarith
  have hlt' : ENNReal.ofReal ((a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ) < ENNReal.ofReal (b₁ * τ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt
  have hfin : (k : ℝ≥0∞) ≤ ENNReal.ofReal ((a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ) := by
    rcases min_le_iff.mp (hlow.trans hup) with h | h
    · exact hA.trans h
    · exact absurd (hB.trans h) (not_le.mpr hlt')
  rw [← ENNReal.ofReal_natCast] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff hVr).mp hfin

end

theorem lemmaCValRam_proof : LemmaCValRam := by
  intro O _ _ _ ϖ hϖ e he ℓ hℓ E u hEis hu ell g a b₀ b₁ s₀ s₁ k hs h1 h2 hmem
  have hℓ0 : (0:ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have he0 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hA0 : (0:ℝ) ≤ (a : ℝ) + 2 * e * g * ell := by positivity
  have hc0 : (0:ℝ) ≤ (b₀ : ℝ) / ℓ := div_nonneg (Nat.cast_nonneg _) hℓ0.le
  have h2r : (2:ℝ) * b₀ ≤ ℓ * b₁ := by exact_mod_cast h2
  have h2' : 2 * ((b₀ : ℝ) / ℓ) ≤ b₁ := by
    rw [← mul_div_assoc, div_le_iff₀ hℓ0]; linarith
  have hb1 : (0:ℝ) < b₁ := by
    rcases Nat.eq_zero_or_pos b₁ with hb | hb
    · subst hb
      simp only [Nat.cast_zero, mul_zero] at h1
      linarith
    · exact_mod_cast hb
  have hD0 : (0:ℝ) < (b₁:ℝ) - b₀ / ℓ := by linarith
  have hAD : ((a : ℝ) + 2 * e * g * ell) / ((b₁:ℝ) - b₀ / ℓ) < e := by
    rw [div_lt_iff₀ hD0]
    nlinarith [mul_le_mul_of_nonneg_left (show (b₁:ℝ) ≤ 2 * ((b₁:ℝ) - b₀ / ℓ) by linarith)
      (by linarith : (0:ℝ) ≤ e)]
  have key : ∀ τ : ℝ, ((a : ℝ) + 2 * e * g * ell) / ((b₁:ℝ) - b₀ / ℓ) < τ → τ ≤ e →
      (k : ℝ) ≤ (a : ℝ) + 2 * e * g * ell + b₀ / ℓ * τ := by
    intro τ hτ hτe
    have hτ0 : 0 < τ := lt_of_le_of_lt (div_nonneg hA0 hD0.le) hτ
    rw [div_lt_iff₀ hD0] at hτ
    exact cvr_step hϖ he hℓ E u hEis hu hs hmem hτ0 hτe (by nlinarith)
  generalize (a : ℝ) + 2 * e * g * ell = A at hA0 h1 hAD key ⊢
  generalize (b₀ : ℝ) / ℓ = c at hc0 h2' hD0 hAD key ⊢
  generalize (b₁ : ℝ) = B at h1 h2' hb1 hD0 hAD key ⊢
  have hmain : (k : ℝ) ≤ A + c * (A / (B - c)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min ((e:ℝ) - A / (B - c)) (ε / (c + 1)) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]; exact lt_min (by linarith) (div_pos hε (by linarith))
    have hδ1 : δ ≤ (e:ℝ) - A / (B - c) := by rw [hδdef]; exact min_le_left _ _
    have hδ2 : δ ≤ ε / (c + 1) := by rw [hδdef]; exact min_le_right _ _
    have hk := key (A / (B - c) + δ) (by linarith) (by linarith)
    have hcδ : c * δ ≤ ε := by
      calc c * δ ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hδ2 hc0
        _ ≤ ε := by rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hD : A + c * (A / (B - c)) = A * B / (B - c) := by
    have hne : B - c ≠ 0 := hD0.ne'
    first
    | (field_simp; ring)
    | field_simp
  refine ⟨hmain.trans hD.le, (hmain.trans hD.le).trans ?_⟩
  rw [div_le_iff₀ hD0]
  nlinarith [mul_le_mul_of_nonneg_left h2' hA0]

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
