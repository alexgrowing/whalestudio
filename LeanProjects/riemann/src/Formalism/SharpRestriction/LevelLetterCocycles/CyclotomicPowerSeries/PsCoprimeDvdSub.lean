import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem powerSeries_algHom_C' {O : Type} [CommRing O] (ψ : PowerSeries O →ₐ[O] PowerSeries O) (c : O) :
    ψ (C c) = C c := by
  first
  | exact ψ.commutes c
  | (have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by
       rw [PowerSeries.smul_eq_C_mul, mul_one]
     rw [e, map_smul, map_one])
  | simpa using ψ.commutes c

theorem psCoprime_dvdSub {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    (X * (X + C (l : O)) : PowerSeries O) ∣ φ a - C (constantCoeff a) := by
  obtain ⟨b, hb⟩ : (X : PowerSeries O) ∣ a - C (constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have e : φ (a - C (constantCoeff a)) = φ a - C (constantCoeff a) := by
    rw [map_sub, powerSeries_algHom_C']
  rw [← e, hb, map_mul]
  exact dvd_mul_of_dvd_left h _

private theorem constantCoeff_algHom_eq_of_X_mul_dvd {O : Type} [CommRing O] (l : ℕ)
    (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    constantCoeff (φ a) = constantCoeff a := by
  have h1 := psCoprime_dvdSub l φ h a
  have h2 : (X : PowerSeries O) ∣ φ a - C (constantCoeff a) :=
    dvd_trans (dvd_mul_right (X : PowerSeries O) _) h1
  rw [PowerSeries.X_dvd_iff] at h2
  first
  | simpa [sub_eq_zero] using h2
  | (rw [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h2; exact h2)

theorem psCoprime_cc {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s : ℕ) :
    constantCoeff ((⇑φ)^[s] (X + C (l : O))) = (l : O) := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', constantCoeff_algHom_eq_of_X_mul_dvd l φ h, ih]

theorem psCoprime_qdvd {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (t : ℕ) :
    (X + C (l : O) : PowerSeries O) ∣ (⇑φ)^[t + 1] (X + C (l : O)) - C (l : O) := by
  rw [Function.iterate_succ_apply']
  have h1 := psCoprime_dvdSub l φ h ((⇑φ)^[t] (X + C (l : O)))
  rw [psCoprime_cc l φ h t] at h1
  exact dvd_trans (dvd_mul_left _ _) h1

private theorem algHom_iterate_C_add_mul {O : Type} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (c : O) (s : ℕ) (b d : PowerSeries O) :
    (⇑φ)^[s] (C c + b * d) = C c + (⇑φ)^[s] b * (⇑φ)^[s] d := by
  induction s with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, map_add, map_mul, powerSeries_algHom_C']

theorem psCoprime_lt {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s s' : ℕ) (hs : s < s') :
    (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), (⇑φ)^[s'] (X + C (l : O))} := by
  obtain ⟨t, rfl⟩ : ∃ t, s' = s + (t + 1) := ⟨s' - s - 1, by omega⟩
  obtain ⟨q, hq⟩ := psCoprime_qdvd l φ h t
  have hq' : (⇑φ)^[t + 1] (X + C (l : O)) = C (l : O) + (X + C (l : O)) * q := by
    linear_combination hq
  have e : (⇑φ)^[s + (t + 1)] (X + C (l : O)) =
      C (l : O) + (⇑φ)^[s] (X + C (l : O)) * (⇑φ)^[s] q := by
    rw [Function.iterate_add_apply, hq', algHom_iterate_C_add_mul]
  rw [Ideal.mem_span_pair]
  exact ⟨-((⇑φ)^[s] q), 1, by linear_combination e⟩

theorem psCoprime : PsCoprimeStatement := by
  unfold PsCoprimeStatement
  intro O _ l φ h
  refine ⟨fun s => ?_, fun s s' hss => ?_⟩
  · have hc := psCoprime_cc l φ h s
    obtain ⟨r, hr⟩ : (X : PowerSeries O) ∣ (⇑φ)^[s] (X + C (l : O)) - C (l : O) := by
      rw [PowerSeries.X_dvd_iff, map_sub, hc]
      first
      | simp
      | rw [PowerSeries.constantCoeff_C, sub_self]
    rw [Ideal.mem_span_pair]
    exact ⟨1, -r, by linear_combination hr⟩
  · rcases Nat.lt_or_gt_of_ne hss with hlt | hlt
    · exact psCoprime_lt l φ h s s' hlt
    · rw [Set.pair_comm]
      exact psCoprime_lt l φ h s' s hlt

end LevelStatements.Lv
