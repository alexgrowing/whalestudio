import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qn19.AIC :
    (A : Type) → [CommRing A] → Prop :=
    fun (A : Type) [CommRing A] ↦
      ∀ (p : Polynomial A), p.Monic → (0 : ℕ) < p.natDegree → ∃ (a : A), Polynomial.eval a p = (0 : A)

private theorem UpperTheory.Reformulated.B.Qn19.commonDenom {R L : Type} [CommRing R] [CommRing L] (φ : R →+* L)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) (s : Finset L) :
    ∃ b : R, IsUnit (φ b) ∧ ∀ z ∈ s, ∃ a : R, φ a = z * φ b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x s _ ih =>
    obtain ⟨b, hb, hs⟩ := ih
    obtain ⟨a, c, hc, hx⟩ := h x
    refine ⟨b * c, by rw [map_mul]; exact hb.mul hc, ?_⟩
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨a * b, by rw [map_mul, map_mul, ← hx]; ring⟩
    · obtain ⟨d, hd⟩ := hs z hz
      exact ⟨d * c, by rw [map_mul, map_mul, hd]; ring⟩

theorem UpperTheory.Reformulated.B.Qn19.aicFrac :
    ∀ (R L : Type) [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      UpperTheory.Reformulated.B.Qn19.AIC R →
        (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) → UpperTheory.Reformulated.B.Qn19.AIC L := by
  intro R L _ _ φ hR h p hp hdeg
  obtain ⟨b, hb, hs⟩ := UpperTheory.Reformulated.B.Qn19.commonDenom φ h p.coeffs
  have hmon : (p.scaleRoots (φ b)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hlift : p.scaleRoots (φ b) ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · by_cases h0 : p.coeff i = 0
      · exact ⟨0, by simp [h0]⟩
      · obtain ⟨a, ha⟩ := hs _ (Polynomial.coeff_mem_coeffs h0)
        obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
        exact ⟨a * b ^ k, by rw [map_mul, map_pow, ha, hk]; ring⟩
    · subst hi
      exact ⟨1, by simp [hp.coeff_natDegree]⟩
    · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
  obtain ⟨q, hq, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  rw [Polynomial.natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hR q hqm (by rw [hqd]; exact hdeg)
  obtain ⟨u, hu⟩ := hb
  refine ⟨(↑u⁻¹ : L) * φ a, ?_⟩
  have h1 : Polynomial.eval (φ a) (p.scaleRoots (φ b)) = 0 := by
    rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, ha, map_zero]
  have h2 := Polynomial.scaleRoots_eval_mul p ((↑u⁻¹ : L) * φ a) (φ b)
  have h3 : φ b * ((↑u⁻¹ : L) * φ a) = φ a := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1, ← hu] at h2
  exact ((u.isUnit.pow p.natDegree).mul_right_eq_zero).1 h2.symm
