import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

open Polynomial in

theorem coefO_dvd_pow_l {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O)
    (h0 : x ≠ 0) : ∃ k : ℕ, ∃ u ∈ c.O, x * u = ((l : ℕ) : Qbar l) ^ k := by
  haveI := c.fin
  haveI := c.dvr
  set x' : c.O := ⟨x, hx⟩
  have hx0 : x' ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hint : IsIntegral ℤ_[l] x' := Algebra.IsIntegral.isIntegral x'
  obtain ⟨p, hpm, hp⟩ := hint
  rw [← aeval_def] at hp
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  rw [X_dvd_iff] at hq
  have hqx : aeval x' q = 0 := by
    rw [hpq, map_mul, map_pow, aeval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hx0)
  obtain ⟨r, hr⟩ := (X_dvd_sub_C : X ∣ q - C (q.coeff 0))
  have hrel : algebraMap ℤ_[l] c.O (q.coeff 0) = x' * (-(aeval x' r)) := by
    have := congrArg (aeval x') hr
    rw [map_sub, aeval_C, map_mul, aeval_X, hqx] at this
    linear_combination -this
  set a := q.coeff 0 with ha
  set w : ℤ_[l]ˣ := PadicInt.unitCoeff hq
  have hspec : a = (w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation := PadicInt.unitCoeff_spec hq
  have haw : a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (l : ℤ_[l]) ^ a.valuation := by
    calc a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
        = ((w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by rw [← hspec]
      _ = (l : ℤ_[l]) ^ a.valuation := by
        rw [mul_comm, ← mul_assoc]; simp
  refine ⟨a.valuation, (((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : c.O) : Qbar l),
    Subtype.property _, ?_⟩
  have h2 : x' * ((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]))
      = algebraMap ℤ_[l] c.O ((l : ℤ_[l]) ^ a.valuation) := by
    rw [← mul_assoc, ← hrel, ← map_mul, haw]
  have h3 := congrArg Subtype.val h2
  simpa using h3

end GlobalTheory

namespace GlobalTheory

theorem rat_unram_to_int_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∃ m : ℕ, ∀ (Y : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Y s i ∈ c.O) → (∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, (((l : ℕ) : Qbar l) ^ m) • Y s = mat W s *ᵥ t - t := by
  intro l _ Ω _ _ W c B _hW hWO
  let A : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l) := fun s => mat W s - 1
  have hAO : ∀ s i j, A s i j ∈ c.O := by
    intro s i j
    simp only [A, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact sub_mem (hWO s i j) (one_mem _)
    · simpa using hWO s i j
  have hmv : ∀ s (w : Fin 2 → Qbar l) i,
      (mat W s *ᵥ w - w) i = A s i 0 * w 0 + A s i 1 * w 1 := by
    intro s w i
    rw [show mat W s *ᵥ w - w = A s *ᵥ w by simp [A, Matrix.sub_mulVec]]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  by_cases h2 : ∃ s ∈ Ine (F := ℚ) B, ∃ s' ∈ Ine (F := ℚ) B, ∃ i i' : Fin 2,
      A s i 0 * A s' i' 1 - A s i 1 * A s' i' 0 ≠ 0
  · obtain ⟨s, hs, s', hs', i, i', hd⟩ := h2
    obtain ⟨k, u, hu, hdu⟩ := coefO_dvd_pow_l c
      (sub_mem (mul_mem (hAO s i 0) (hAO s' i' 1)) (mul_mem (hAO s i 1) (hAO s' i' 0))) hd
    refine ⟨k, fun Y v hY hYv => ⟨((l : ℕ) : Qbar l) ^ k • v, ?_, ?_⟩⟩
    · have hP := hY s i
      have hQ := hY s' i'
      rw [hYv s hs, hmv] at hP
      rw [hYv s' hs', hmv] at hQ
      intro j
      fin_cases j
      · have e : ((l : ℕ) : Qbar l) ^ k • v 0 = u * (A s' i' 1 * (A s i 0 * v 0 + A s i 1 * v 1)
            - A s i 1 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 0)) * hdu
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hP) (mul_mem (hAO _ _ _) hQ))
      · have e : ((l : ℕ) : Qbar l) ^ k • v 1 = u * (A s i 0 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)
            - A s' i' 0 * (A s i 0 * v 0 + A s i 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 1)) * hdu
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hQ) (mul_mem (hAO _ _ _) hP))
    · intro s₀ hs₀
      rw [hYv s₀ hs₀, smul_sub, Matrix.mulVec_smul]
  · push_neg at h2
    by_cases h1 : ∃ s ∈ Ine (F := ℚ) B, ∃ i j, A s i j ≠ 0
    · obtain ⟨s, hs, i, j, hα⟩ := h1
      obtain ⟨k, u, hu, hαu⟩ := coefO_dvd_pow_l c (hAO s i j) hα
      refine ⟨k, fun Y v hY hYv => ⟨Pi.single j (u * Y s i), ?_, ?_⟩⟩
      · intro j'
        rcases eq_or_ne j' j with rfl | h
        · simpa using mul_mem hu (hY s i)
        · simp [h]
      · intro s' hs'
        have hc : Y s i = A s i 0 * v 0 + A s i 1 * v 1 := by rw [hYv s hs, hmv]
        ext i'
        rw [Pi.smul_apply, hmv, hYv s' hs', hmv, hc]
        have hdet := h2 s hs s' hs' i i'
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu + u * v 1 * hdet
        · simp only [Fin.mk_one, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu - u * v 0 * hdet
    · push_neg at h1
      refine ⟨0, fun Y v _ hYv => ⟨0, fun _ => zero_mem _, fun s hs => ?_⟩⟩
      ext i
      rw [Pi.smul_apply, hYv s hs, hmv, hmv]
      simp [h1 s hs]

end GlobalTheory
