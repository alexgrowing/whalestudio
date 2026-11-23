import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.H1cEqH1

namespace KStar.Selmer

open Matrix Module

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M']
  [Module (ZMod N) M']

private theorem zmod_dbl_ann (d y : ZMod N) (h : ∀ r : ZMod N, r * d = 0 → r * y = 0) :
    ∃ c : ZMod N, y = c * d := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective d
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective y
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right a N
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a N
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [hm, h0, mul_zero]) (NeZero.ne N)
    · exact h0
  have h1 : (m : ZMod N) * a = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨a', ?_⟩
    calc m * a = m * (a.gcd N * a') := by rw [← ha']
      _ = (a.gcd N * m) * a' := by ring
      _ = N * a' := by rw [← hm]
  have h2 := h _ h1
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h2
  have h3 : a.gcd N * m ∣ b * m := by rw [← hm, mul_comm]; exact h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 h3
  have h4 : ((a.gcd N : ℕ) : ZMod N) = (a : ZMod N) * ((Nat.gcdA a N : ℤ) : ZMod N) := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) (Nat.gcd_eq_gcd_ab a N)
    simpa using this
  refine ⟨((Nat.gcdA a N : ℤ) : ZMod N) * k, ?_⟩
  rw [hk, Nat.cast_mul, h4]
  ring

omit [NeZero N] in
private theorem zmod_ideal_gen (I : Ideal (ZMod N)) :
    ∃ d ∈ I, ∀ x ∈ I, ∃ r : ZMod N, x = r * d := by
  have : IsPrincipalIdealRing (ZMod N) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod N)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal I).principal
  refine ⟨d, hd ▸ Submodule.mem_span_singleton_self d, fun x hx => ?_⟩
  rw [hd, Submodule.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

theorem zmod_baer : Module.Baer (ZMod N) (ZMod N) := by
  intro I g
  obtain ⟨d, hd, hI⟩ := zmod_ideal_gen I
  obtain ⟨c, hc⟩ := zmod_dbl_ann d (g ⟨d, hd⟩) (fun r hr => by
    have : r • (⟨d, hd⟩ : I) = 0 := Subtype.ext hr
    rw [← smul_eq_mul, ← map_smul, this, map_zero])
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := hI x hx
  have : (⟨r * d, hx⟩ : I) = r • (⟨d, hd⟩ : I) := rfl
  rw [this, map_smul, hc, LinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]
  ring

private theorem zmod_extend {A B : Type*} [AddCommGroup A] [Module (ZMod N) A] [AddCommGroup B]
    [Module (ZMod N) B] (φ : A →ₗ[ZMod N] B) (c : A →ₗ[ZMod N] ZMod N)
    (h : ∀ a, φ a = 0 → c a = 0) : ∃ t : B →ₗ[ZMod N] ZMod N, ∀ a, t (φ a) = c a := by
  obtain ⟨t, ht⟩ := (zmod_baer (N := N)).extension_property
    ((LinearMap.ker φ).liftQ φ le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker φ).liftQ c (fun a ha => h a ha))
  refine ⟨t, fun a => ?_⟩
  exact LinearMap.congr_fun ht (Submodule.Quotient.mk a)

theorem exists_form_ne_zero (I : Submodule (ZMod N) M) {z : M} (hz : z ∉ I) :
    ∃ f : M →ₗ[ZMod N] ZMod N, (∀ x ∈ I, f x = 0) ∧ f z ≠ 0 := by
  obtain ⟨d, hd, hI⟩ :=
    zmod_ideal_gen (LinearMap.ker (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z)))
  have hw : ∃ w : ZMod N, w * d = 0 ∧ w ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨c, hc⟩ := zmod_dbl_ann d 1 (fun r hr => by rw [hne r hr, zero_mul])
    have h0 : d • I.mkQ z = 0 := hd
    have h1 : I.mkQ z = 0 := by
      rw [← one_smul (ZMod N) (I.mkQ z), hc, mul_smul, h0, smul_zero]
    exact hz (by simpa using h1)
  obtain ⟨w, hw, hw0⟩ := hw
  obtain ⟨t, ht⟩ := zmod_extend (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z))
    (LinearMap.toSpanSingleton (ZMod N) (ZMod N) w) (fun a ha => by
      obtain ⟨r, rfl⟩ := hI a ha
      rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc, mul_comm d w, hw, mul_zero])
  refine ⟨t ∘ₗ I.mkQ, fun x hx => ?_, ?_⟩
  · have : I.mkQ x = 0 := by simpa using hx
    rw [LinearMap.comp_apply, this, map_zero]
  · have := ht 1
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, one_smul, one_smul] at this
    rw [LinearMap.comp_apply, this]
    exact hw0

end KStar.Selmer
