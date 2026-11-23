import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x1

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem conj_real (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

theorem smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

end Formalism.FourierDecayAlt.P.S6x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem unramRelative : Formalism.FourierDecayAlt.S6.UnramRelative := by
  intro E _ _ _ hU
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (maximalRealSubfield E)) (𝓞 E)
  unfold Unram at hU
  have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
    rw [← hU]; exact differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  refine ⟨h1, fun g => ?_⟩
  unfold UnramAbove
  rw [h1, Ideal.isCoprime_iff_sup_eq]; simp

theorem degreeFacts_statement : Formalism.FourierDecayAlt.S6.DegreeFacts := by
  intro E _ _ _
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : 0 < finrank ℚ (maximalRealSubfield E) := finrank_pos
  rw [h2] at h3
  refine ⟨by unfold deg; omega, ?_, h4⟩
  have h5 := IsTotallyComplex.finrank E
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  unfold deg
  omega

theorem localAwayFromLevel : Formalism.FourierDecayAlt.S6.LocOrdinary := by
  intro E _ _ _ g k ν P hP hg
  have hg0 : (g : E) ≠ 0 := by
    intro h
    apply hg
    have : g = 0 := by exact_mod_cast h
    simp [this]
  have key : ∀ (k k' : ℤ) (t : E), t ∈ locAt E P (zsub E (idl E g k ν)) →
      t ∈ locAt E P (zsub E (idl E g k' ν)) := by
    intro k k' t
    rintro ⟨a, ha, h⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k' ≤ k + n := ⟨(k' - k).toNat, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k + n = k' + m := ⟨(k + n - k').toNat, by omega⟩
    refine ⟨(g : 𝓞 (maximalRealSubfield E)) ^ n * a,
      fun hh => (hP.mem_or_mem hh).elim (fun h' => hg (hP.mem_of_pow_mem _ h')) ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k' ν
    unfold idl at h ⊢
    rw [mul_comm, FractionalIdeal.mem_singleton_mul] at h ⊢
    obtain ⟨z, hz, hh⟩ := h
    refine ⟨(g : E) ^ m * z, ?_, ?_⟩
    · have := (dd E ^ ν : FI E).coeToSubmodule.smul_mem ((g : 𝓞 E) ^ m) hz
      rw [Algebra.smul_def] at this
      simpa using this
    · rw [map_mul, mul_assoc, hh, map_pow, map_natCast, ← mul_assoc, ← mul_assoc, ← zpow_natCast,
        ← zpow_natCast, ← zpow_add₀ hg0, ← zpow_add₀ hg0, add_comm (n : ℤ) k, hm]
  ext t
  exact ⟨key _ _ t, key _ _ t⟩

theorem localTwistedLattice : Formalism.FourierDecayAlt.S6.LocTw := by
  intro E _ _ _ A B s P hP t
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_twLat] at h
    refine ⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩
    have := h.2
    rw [map_mul, conj_real] at this
    show _ ∈ B
    convert this using 1; ring
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
    rw [mem_twLat]
    constructor
    · have := smul_mem_FI E A b _ h1
      rw [map_mul]; convert this using 1; ring
    · have := smul_mem_FI E B a _ h2
      rw [map_mul, map_mul, map_mul, conj_real, conj_real]; convert this using 1; ring

theorem scaledIdealNorm : Formalism.FourierDecayAlt.S6.NormIdl := by
  intro E _ _ _ g k ν hg
  have hdeg := degreeFacts_statement E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hrd : 0 < rd E := by
    unfold rd
    apply Real.rpow_pos_of_pos
    have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
    exact_mod_cast this
  have hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E) := by
    unfold rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]
    have : ((2 * deg E : ℕ) : ℝ) ≠ 0 := by
      have := hdeg.2.2
      positivity
    rw [inv_mul_cancel₀ this, Real.rpow_one]
  have h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ) := by
    unfold dd
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k))
      = ((g : ℚ) ^ (2 * deg E)) ^ k := by
    rw [FractionalIdeal.absNorm_span_singleton,
      show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast],
      Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold idl
  rw [map_mul, map_zpow₀, h1, h2]
  push_cast
  have hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E) := by rw [← hD]; push_cast; rfl
  rw [hD']
  have : (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k
      = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2 := by
    rw [← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow,
      ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]
    congr 2 <;> (push_cast; ring)
  rw [this, Real.sqrt_sq (by positivity)]

theorem discrSquare : Formalism.FourierDecayAlt.S6.DiscrSquare := by
  intro E _ _ _ h
  have := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  rw [(unramRelative E h).1, Algebra.IsQuadraticExtension.finrank_eq_two] at this
  simpa using this

theorem twistedLatticeBetween : Formalism.FourierDecayAlt.S6.Between := by
  intro E _ _ _ A B s hBA hB
  refine ⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩
  rw [mem_twLat]
  refine ⟨hBA ht, ?_⟩
  have h1 : complexConj E t ∈ B := hB t ht
  have h2 : (-1 : E) ^ s * complexConj E t ∈ B := by
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · simpa using h1
    · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
  exact B.coeToSubmodule.sub_mem ht h2

theorem dualIdealEqLiftIdeal : Formalism.FourierDecayAlt.S6.IdealsMatch := by
  intro E _ _ _ g r i s
  refine ⟨?_, ?_, ?_⟩
  · unfold dualIdl liftIdl nuBlock; congr 1; ring
  · unfold dualIdl nuBlock; congr 1; ring
  · unfold nuBlock; ring

theorem periodLatticeFactsSplitOfGeneral : Formalism.FourierDecayAlt.S6.TextFromGeneral := by
  intro h E _ _ _ hU g₁ g₂ h₁ h₂ ν s _
  exact h E hU _ ν s (Nat.mul_pos h₁.1.pos h₂.1.pos)

end Formalism.FourierDecayAlt.P
