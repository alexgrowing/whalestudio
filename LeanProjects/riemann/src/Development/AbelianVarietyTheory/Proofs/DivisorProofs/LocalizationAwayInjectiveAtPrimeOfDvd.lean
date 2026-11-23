import Mathlib

namespace GlobalTheory

theorem localization_away_injective_of_dvd (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
      Function.Injective κ := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R (Localization.AtPrime 𝔭)) with hI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  have key : ∀ s : Finset R, (∀ x ∈ s, algebraMap R (Localization.AtPrime 𝔭) x = 0) →
      ∃ t ∉ 𝔭, ∀ x ∈ s, t * x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨t, ht, hts⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) a).mp
        (h a (Finset.mem_insert_self a s))
      refine ⟨(m : R) * t, 𝔭.primeCompl.mul_mem m.2 ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm (m : R) t, mul_assoc, hm, mul_zero]
      · rw [mul_assoc, hts x hx, mul_zero]
  obtain ⟨t, ht, hts⟩ := key s (fun x hx => by
    have : x ∈ I := hs ▸ Submodule.subset_span hx
    simpa [hI] using this)
  have hker : ∀ x ∈ I, t * x = 0 := by
    have hle : I ≤ LinearMap.ker (LinearMap.mulLeft R t) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp [hts x hx]
    intro x hx
    simpa using hle hx
  refine ⟨t, ht, ?_⟩
  intro c ⟨d, hd⟩ κ hκ
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) x
  have hspec := IsLocalization.mk'_spec (Localization.Away c) a m
  have h1 : algebraMap R (Localization.AtPrime 𝔭) a = 0 := by
    have := congrArg κ hspec
    rw [map_mul, hx, zero_mul] at this
    rw [← hκ, RingHom.comp_apply, ← this]
  have hta : t * a = 0 := hker a (by simpa [hI] using h1)
  have hu : IsUnit (algebraMap R (Localization.Away c) t) := by
    have hc := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    have hc' : IsUnit (algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) d) := by
      rw [← map_mul, ← hd]; exact hc
    exact isUnit_of_mul_isUnit_left hc'
  have ha : algebraMap R (Localization.Away c) a = 0 := by
    have : algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) a = 0 := by
      rw [← map_mul, hta, map_zero]
    exact (hu.mul_right_eq_zero).mp this
  show IsLocalization.mk' (Localization.Away c) a m = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]

end GlobalTheory
