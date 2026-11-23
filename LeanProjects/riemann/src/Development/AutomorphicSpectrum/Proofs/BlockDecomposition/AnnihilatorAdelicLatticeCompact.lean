import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import GroundTheory.GlobalFields.Adele.Compact
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.AnnLattice

variable {E : Type} [Field E] [NumberField E]

theorem sLoc_mul (w : Pl E) (t : w.adicCompletion E) (z : Af E) :
    sLoc E w t * z = sLoc E w (t * pLoc E w z) := by
  classical
  refine FiniteAdeleRing.ext _ fun v => ?_
  change (Pi.single w t : ∀ v : Pl E, v.adicCompletion E) v * pLoc E v z =
    (Pi.single w (t * pLoc E w z) : ∀ v : Pl E, v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem val_int_le_one (u : Pl E) (d : 𝓞 E) :
    Valued.v (algebraMap E (u.adicCompletion E) (algebraMap (𝓞 E) E d)) ≤ 1 := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap]
  exact u.valuation_le_one d

theorem exists_int_small (S : Finset (Pl E)) (c : Pl E → WithZero (Multiplicative ℤ))
    (hc : ∀ w ∈ S, c w ≠ 0) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ w ∈ S, Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D)) ≤ c w := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert w S hw ih =>
    obtain ⟨D, hD0, hD⟩ := ih fun u hu => hc u (Finset.mem_insert_of_mem hu)
    obtain ⟨x, hxw, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hlt : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E x)) < 1 := by
      rw [Formalism.UG.P.levelaf_valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hxw
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (hc w (Finset.mem_insert_self _ _)))
    refine ⟨D * x ^ n, mul_ne_zero hD0 (pow_ne_zero _ hx0), fun u hu => ?_⟩
    simp only [map_mul, map_pow]
    rcases Finset.mem_insert.1 hu with rfl | hu
    · calc _ ≤ 1 * _ := mul_le_mul' (val_int_le_one u D) le_rfl
        _ = _ := one_mul _
        _ ≤ c u := hn.le
    · calc _ ≤ c u * 1 := mul_le_mul' (hD u hu) (pow_le_one' (val_int_le_one u x) n)
        _ = c u := mul_one _

theorem one_le_exp_mul {b : WithZero (Multiplicative ℤ)} (h : 1 < b) : 1 ≤ WithZero.exp (-1 : ℤ) * b := by
  have hb0 : b ≠ 0 := (zero_lt_one.trans h).ne'
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, b = WithZero.exp n := ⟨_, (WithZero.exp_log hb0).symm⟩
  rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

variable {ψ : AddChar (Ad E) ℂ}

theorem val_le_one_of_cond {w : Pl E} (hw : Cond ψ w) {L : Set (Af E)}
    (hL : ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) {z : Af E}
    (hz : ∀ a ∈ L, ψ (sFin E (a * z)) = 1) : Valued.v (pLoc E w z) ≤ 1 := by
  by_contra hcon
  have h1 : 1 < Valued.v (pLoc E w z) := not_le.1 hcon
  obtain ⟨-, ϖ, y, hϖ, hy1, hy⟩ := hw
  have hz0 : Valued.v (pLoc E w z) ≠ 0 := (zero_lt_one.trans h1).ne'
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hz0
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hd : 1 ≤ Valued.v ϖ * Valued.v (pLoc E w z) := by
    rw [hϖ']
    exact one_le_exp_mul h1
  have hyv : Valued.v (ϖ * y) ≤ 1 := hy1
  rw [map_mul] at hyv
  have hle : Valued.v y ≤ Valued.v (pLoc E w z) := by
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ ≤ (Valued.v ϖ * Valued.v (pLoc E w z)) * Valued.v y := mul_le_mul' hd le_rfl
      _ = (Valued.v ϖ * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ 1 * Valued.v (pLoc E w z) := mul_le_mul' hyv le_rfl
      _ = _ := one_mul _
  have ht : y / pLoc E w z ∈ Formalism.UG.Ov E w := by
    change Valued.v (y / pLoc E w z) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_val_bound (hψ : StdPsi ψ) (w : Pl E) {L : Set (Af E)} {N : Set (w.adicCompletion E)} (hN : N ∈ 𝓝 0)
    (hL : ∀ t ∈ N, sLoc E w t ∈ L) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) →
      ∀ d : w.adicCompletion E, Valued.v d ≤ c → Valued.v (d * pLoc E w z) ≤ 1 := by
  obtain ⟨y, hy⟩ := hψ.loc w
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  have hY : Valued.v y ≠ 0 := (map_ne_zero _).2 hy0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hN
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨g / Valued.v y, div_ne_zero hg0 hY, fun z hz d hd => ?_⟩
  by_contra hcon
  have h1 : 1 < Valued.v (d * pLoc E w z) := not_le.1 hcon
  rw [map_mul] at h1
  have hb0 : Valued.v (pLoc E w z) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact not_lt_of_ge zero_le' h1
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hb0
  have hYpos : 0 < Valued.v y := zero_lt_iff.2 hY
  have hbpos : 0 < Valued.v (pLoc E w z) := zero_lt_iff.2 hb0
  have hdY : Valued.v d * Valued.v y ≤ g := (le_div_iff₀ hYpos).1 hd
  have ht : y / pLoc E w z ∈ N := by
    refine hγ ?_
    change (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (y / pLoc E w z) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_div₀, ← hg, div_lt_iff₀ hbpos]
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ < (Valued.v d * Valued.v (pLoc E w z)) * Valued.v y := mul_lt_mul_of_pos_right h1 hYpos
      _ = (Valued.v d * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ g * Valued.v (pLoc E w z) := mul_le_mul' hdY le_rfl
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_isCompact_annihilator : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ},
    StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)),
    (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) →
    (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) →
    ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  intro E _ _ _ ψ hψ S hS L hoff hon
  classical
  have hloc : ∀ w : Pl E, ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ (w ∈ S → ∀ z : Af E,
      (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → ∀ d : w.adicCompletion E, Valued.v d ≤ c →
        Valued.v (d * pLoc E w z) ≤ 1) := fun w => by
    by_cases hw : w ∈ S
    · obtain ⟨N, hN, hNL⟩ := hon w hw
      obtain ⟨c, hc0, hc⟩ := exists_val_bound hψ w hN hNL
      exact ⟨c, hc0, fun _ => hc⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose c hc0 hc using hloc
  obtain ⟨D, hD0, hD⟩ := exists_int_small S c fun w _ => hc0 w
  have he : algebraMap (𝓞 E) E D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hD0
  refine ⟨(fun y => algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id), fun z hz => ?_⟩
  refine ⟨algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z, ?_, ?_⟩
  · refine SetLike.mem_coe.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_)
    have e : (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) w =
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D) * pLoc E w z := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ S
    · exact hc w hw z hz _ (hD w hw)
    · rw [map_mul]
      calc _ ≤ 1 * 1 := mul_le_mul' (val_int_le_one w D) (val_le_one_of_cond (hS w hw) (hoff w hw) hz)
        _ = 1 := one_mul 1
  · change algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) = z
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul]

end GlobalTheory.CompanionTheory.AnnLattice

end
