import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield GlobalTheory.PlaceComponents

namespace GlobalTheory.ApproxIdem

theorem improve {O F : Type*} [CommRing O] [NormedField F] (f g : O →+* F) (hf : ∀ a, ‖f a‖ ≤ 1)
    (hg : ∀ a, ‖g a‖ ≤ 1) (r : ℝ) (e : O) (h1 : ‖f e - 1‖ ≤ r) (h2 : ‖g e‖ ≤ r) (m : ℕ) :
    ∃ ε : O, ‖f ε - 1‖ ≤ r ^ m ∧ ‖g ε‖ ≤ r ^ m := by
  refine ⟨1 - (1 - e ^ m) ^ m, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow 1 e m
    rw [one_pow] at hc
    rw [hc]
    have : f (1 - ((1 - e) * c) ^ m) - 1 = -((-(f e - 1)) * f c) ^ m := by
      simp only [map_sub, map_one, map_pow, map_mul]; ring
    rw [this, norm_neg, norm_pow, norm_mul, norm_neg]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    exact (mul_le_of_le_one_right (norm_nonneg _) (hf c)).trans h1
  · obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow 1 (1 - e ^ m) m
    rw [one_pow, sub_sub_cancel] at hc
    rw [hc, map_mul, norm_mul, map_pow, norm_pow]
    exact (mul_le_of_le_one_right (by positivity) (hg c)).trans (pow_le_pow_left₀ (norm_nonneg _) h2 m)

theorem dichotomy {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) (k n : ℤ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hs : a + b = 1 + p * k) (hp : a * b = p * n) :
    (‖a - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖b‖ ≤ (p : ℝ)⁻¹) ∨ (‖b - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖a‖ ≤ (p : ℝ)⁻¹) := by
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [h, norm_algebraMap', Padic.norm_p]
  have hz : ∀ z : ℤ, ‖(p : ℂ_[p]) * z‖ ≤ (p : ℝ)⁻¹ := fun z => by
    rw [norm_mul, hpn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_intCast_le_one _ z)
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have key : ∀ a b : ℂ_[p], a + b = 1 + p * k → a * b = p * n → ‖a‖ = 1 →
      ‖a - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖b‖ ≤ (p : ℝ)⁻¹ := fun a b hs hp h => by
    have h2 : ‖b‖ ≤ (p : ℝ)⁻¹ := by
      have := hz n
      rwa [← hp, norm_mul, h, one_mul] at this
    refine ⟨?_, h2⟩
    have : a - 1 = (p : ℂ_[p]) * k + -b := by linear_combination hs
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (by rwa [norm_neg]))
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (key a b hs hp h)
  rcases hb.eq_or_lt with h' | h'
  · exact Or.inr (key b a (by rw [add_comm, hs]) (by rw [mul_comm, hp]) h')
  exfalso
  have h1 : (1 : ℂ_[p]) = (a + b) + -((p : ℂ_[p]) * k) := by linear_combination -hs
  have h2 : ‖(1 : ℂ_[p])‖ < 1 := by
    rw [h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h h')
    · rw [norm_neg]; exact (hz k).trans_lt hlt
  simp at h2

theorem exists_trace_one (D : D7) (p : ℕ) [Fact p.Prime] (h : Formalism.L2.Ker.SplitK D p) :
    ∃ (e : 𝓞 D.host.K) (k n : ℤ), (e : D.host.K) + conjK D e = 1 + p * k ∧ (e : D.host.K) * conjK D e = p * n := by
  obtain ⟨-, σ, θ, hσ, hθ, hσθ, -, hint, -⟩ := quadratic_subfield D
  have e : conjK D θ = -θ := (Subtype.ext (hσ θ).symm : conjK D θ = σ θ).trans hσθ
  by_cases h2 : p = 2
  · subst h2
    have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by omega⟩
    have hm' : (D.host.d : D.host.K) + 1 = 8 * (m : D.host.K) := by exact_mod_cast hm
    refine ⟨⟨(1 + θ) / 2, hint⟩, 0, m, ?_, ?_⟩
    · change (1 + θ) / 2 + conjK D ((1 + θ) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat, e]
      push_cast; ring
    · change (1 + θ) / 2 * conjK D ((1 + θ) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat, e]
      push_cast
      linear_combination (-1 / 4 : D.host.K) * hθ + (1 / 4 : D.host.K) * hm'
  · have hj : jacobiSym (-(D.host.d : ℤ)) p = 1 := h.resolve_left h2
    obtain ⟨a, ha⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
      rw [(legendreSym.eq_zero_iff p _).2 (by simpa using ha)] at hj
      exact zero_ne_one hj
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    obtain ⟨A, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨T, hT⟩ := ZMod.intCast_surjective (2 * (A : ZMod p))⁻¹
    obtain ⟨k, hk⟩ : (p : ℤ) ∣ T * (2 * A) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hT, inv_mul_cancel₀ (mul_ne_zero h20 ha0), sub_self]
    obtain ⟨n, hn⟩ : (p : ℤ) ∣ A * A + D.host.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at ha ⊢
      rw [← ha]; ring
    have hθi : IsIntegral ℤ θ := by
      have : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
      rw [this]
      exact (hint.add hint).sub isIntegral_one
    have hk' : (T : D.host.K) * (2 * A) - 1 = p * k := by exact_mod_cast hk
    have hn' : (A : D.host.K) * A + D.host.d = p * n := by exact_mod_cast hn
    have hI : IsIntegral ℤ ((T : D.host.K) * (A + θ)) :=
      (isIntegral_algebraMap (R := ℤ) (x := T)).mul ((isIntegral_algebraMap (R := ℤ) (x := A)).add hθi)
    refine ⟨⟨(T : D.host.K) * (A + θ), hI⟩, k, T ^ 2 * n, ?_, ?_⟩
    · change (T : D.host.K) * (A + θ) + conjK D ((T : D.host.K) * (A + θ)) = _
      rw [map_mul, map_add, map_intCast, map_intCast, e]
      linear_combination hk'
    · change (T : D.host.K) * (A + θ) * conjK D ((T : D.host.K) * (A + θ)) = _
      rw [map_mul, map_add, map_intCast, map_intCast, e]
      push_cast
      linear_combination (T : D.host.K) ^ 2 * hn' - (T : D.host.K) ^ 2 * hθ

theorem exists_isIdem : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Formalism.L2.Ker.SplitK D p →
    ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε := by
  intro D p _ lam h m
  obtain ⟨e, k, n, hs, hp⟩ := exists_trace_one D p h
  have hs' := congrArg (homP D lam) hs
  have hp' := congrArg (homP D lam) hp
  simp only [map_add, map_mul, map_one, map_natCast, map_intCast, homP_conjK] at hs' hp'
  have hex : ∃ e : 𝓞 D.host.K, ‖homP D lam e - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖homPbar D lam e‖ ≤ (p : ℝ)⁻¹ := by
    rcases dichotomy _ _ k n (norm_int_le D _ e) (norm_int_le D _ e) hs' hp' with h | h
    · exact ⟨e, h⟩
    · exact ⟨conjO D e, by rwa [coe_conjO, homP_conjK, homPbar_conjK]⟩
  obtain ⟨e₁, h1, h2⟩ := hex
  obtain ⟨ε, hε⟩ := improve ((homP D lam).comp (algebraMap (𝓞 D.host.K) D.host.K))
    ((homPbar D lam).comp (algebraMap (𝓞 D.host.K) D.host.K)) (norm_int_le D (homP D lam)) (norm_int_le D (homPbar D lam)) _ e₁ h1 h2 m
  refine ⟨ε, (isIdem_iff D lam m ε).2 ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hε

end GlobalTheory.ApproxIdem
