import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeAssociate
open IsLocalRing Polynomial

namespace GlobalTheory.DivDescent

theorem colonStep : ∀ (A' B' : Type) [CommRing A'] [IsNoetherianRing A'] [CommRing B'] [Algebra A' B']
    [Module.Flat A' B'] (b c : B') (s : A'), b * c = algebraMap A' B' s →
    (∀ x : A', (∀ j : A', c ∣ algebraMap A' B' j → ∃ a : A', x * j = s * a) →
      b ∣ algebraMap A' B' x) →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ b c s hbc h
  have hφ : (algebraMap A' B').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hle : (Ideal.span {s}).colon (((Ideal.span {c}).comap (algebraMap A' B') : Ideal A') : Set A') ≤
      (Ideal.span {b}).comap (algebraMap A' B') := by
    intro x hx
    rw [Submodule.mem_colon] at hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply h x
    intro j hj
    have := hx j (by rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton]; exact hj)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [ha]⟩
  refine Ideal.map_mono hle ?_
  rw [GlobalTheory.ideal_map_colon_eq_of_flat (algebraMap A' B') hφ, Submodule.mem_colon]
  intro y hy
  have hy' : y ∈ Ideal.span {c} := Ideal.map_comap_le hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.1 hy'
  rw [Ideal.map_span, Set.image_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  exact ⟨z, by rw [← hbc, mul_assoc]⟩

theorem primeDescent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [CommRing B']
    [IsDomain B'] [IsNoetherianRing B'] [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → algebraMap A' B' s ∈ Q →
    (Q.comap (algebraMap A' B')).height = 1 ∧
      (Q.comap (algebraMap A' B')).map (algebraMap A' B') = Q := by
  intro A' B' _ _ _ _ _ _ _ _ s hs hpr Q hQ hQ1 hsQ
  haveI : Algebra.HasGoingDown A' B' := Algebra.HasGoingDown.of_flat
  haveI hPp : (Q.comap (algebraMap A' B')).IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver (Q.comap (algebraMap A' B')) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.comap (algebraMap A' B')) Q
  have hle1 : (Q.comap (algebraMap A' B')).height ≤ 1 := by rw [← hQ1, h]; exact le_self_add
  have h1 : (Q.comap (algebraMap A' B')).height = 1 := by
    refine le_antisymm hle1 ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hb
    have : s ∈ Q.comap (algebraMap A' B') := hsQ
    rw [hb, Ideal.mem_bot] at this
    exact hs this
  refine ⟨h1, ?_⟩
  haveI hP : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).IsPrime := hpr _ hPp h1 hsQ
  have hle : (Q.comap (algebraMap A' B')).map (algebraMap A' B') ≤ Q := Ideal.map_comap_le
  by_contra hne
  have hlt := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hQ1] at hlt
  have h0 : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp hlt
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  have hm : algebraMap A' B' s ∈ (Q.comap (algebraMap A' B')).map (algebraMap A' B') :=
    Ideal.mem_map_of_mem _ hsQ
  rw [h0, Ideal.mem_bot] at hm
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
    (mem_nonZeroDivisors_of_ne_zero hs)
  have h2 : s • (1 : B') = s • (0 : B') := by
    rw [Algebra.smul_def, mul_one, smul_zero]; exact hm
  exact one_ne_zero (hreg h2)

theorem divisor_descent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [IsIntegrallyClosed A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B']
    [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ _ _ _ _ _ s hs hpr b c hbc
  have hinj : ∀ a : A', a ≠ 0 → algebraMap A' B' a ≠ 0 := by
    intro a ha h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
      (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : a • (1 : B') = a • (0 : B') := by
      rw [Algebra.smul_def, mul_one, smul_zero]; exact h0
    exact one_ne_zero (hreg h1)
  have hb0 : b ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, zero_mul])
  have hc0 : c ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, mul_zero])
  have hloc : ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → b ∈ Q →
      ∃ j : A', c ∣ algebraMap A' B' j ∧ ∃ t ∉ Q, algebraMap A' B' j ∣ t * c := by
    intro Q hQ hQ1 hbQ
    have hsQ : algebraMap A' B' s ∈ Q := by rw [← hbc]; exact Q.mul_mem_right c hbQ
    obtain ⟨h𝔭1, h𝔭Q⟩ := primeDescent A' B' s hs hpr Q hQ hQ1 hsQ
    obtain ⟨j₀, ⟨t₁, ht₁, hj₁⟩, ⟨t₂, ht₂, hj₂⟩⟩ :=
      GlobalTheory.T.height_one_prime_associate A' B' (Q.comap (algebraMap A' B')) (by rw [h𝔭Q]; exact hQ) (by rw [h𝔭Q]; exact hQ1) c hc0
    rw [h𝔭Q] at ht₁ ht₂
    have hS0 : (0 : B') ∉ (Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B') := by
      intro h0
      obtain ⟨u', hu', h⟩ := Submonoid.mem_map.1 h0
      by_cases hu0 : u' = 0
      · exact hu' (hu0 ▸ (Q.comap (algebraMap A' B')).zero_mem)
      · exact hinj u' hu0 h
    obtain ⟨u, huS, hu⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ((Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B'))
      hS0 (algebraMap A' B' j₀) c hc0 (by
        intro Q' hQ' hQ'1 hcQ' hdisj
        have hsQ' : algebraMap A' B' s ∈ Q' := by rw [← hbc]; exact Q'.mul_mem_left b hcQ'
        obtain ⟨h𝔭'1, h𝔭'Q'⟩ := primeDescent A' B' s hs hpr Q' hQ' hQ'1 hsQ'
        have hle : Q'.comap (algebraMap A' B') ≤ Q.comap (algebraMap A' B') := by
          intro x hx
          by_contra hx𝔭
          exact Set.disjoint_left.1 hdisj (Submonoid.mem_map_of_mem (algebraMap A' B') hx𝔭) hx
        have heq : Q'.comap (algebraMap A' B') = Q.comap (algebraMap A' B') := by
          by_contra hne
          have := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
          rw [h𝔭'1, h𝔭1] at this
          exact lt_irrefl _ this
        have hQQ : Q' = Q := by rw [← h𝔭'Q', heq, h𝔭Q]
        subst hQQ
        exact ⟨t₁, ht₁, hj₁⟩)
    obtain ⟨u', hu', rfl⟩ := Submonoid.mem_map.1 huS
    refine ⟨u' * j₀, by rw [map_mul]; exact hu, algebraMap A' B' u' * t₂, ?_, ?_⟩
    · intro hm
      rcases hQ.mem_or_mem hm with h | h
      · exact hu' h
      · exact ht₂ h
    · rw [map_mul, mul_assoc]; exact mul_dvd_mul_left _ hj₂
  apply colonStep A' B' b c s hbc
  intro x hx
  obtain ⟨u, hu, hdiv⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ⊥ (by simp) (algebraMap A' B' x) b hb0 (by
    intro Q hQ hQ1 hbQ _
    obtain ⟨j, hcj, t, htQ, z, hz⟩ := hloc Q hQ hQ1 hbQ
    obtain ⟨a, ha⟩ := hx j hcj
    refine ⟨t, htQ, ?_⟩
    have hj0 : algebraMap A' B' j ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact htQ (h ▸ Q.zero_mem)
      · exact hc0 h
    have hx' : algebraMap A' B' x * algebraMap A' B' j = b * c * algebraMap A' B' a := by
      rw [← map_mul, ha, map_mul, hbc]
    refine ⟨algebraMap A' B' a * z, mul_left_cancel₀ hj0 ?_⟩
    linear_combination t * hx' + b * algebraMap A' B' a * hz)
  rw [Submonoid.mem_bot] at hu
  subst hu
  simpa using hdiv

end GlobalTheory.DivDescent
