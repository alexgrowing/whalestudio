import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.DeltaMem

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem norm_int_Kur (l : ℕ) [Fact l.Prime] (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : ‖((z : ℤ) : MaximalUnramifiedExtension l)‖ = 1 := by
  have h2 : ‖(z : ℚ_[l])‖ = 1 := by
    have h5 : ‖(z : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp ((PadicInt.norm_int_lt_one_iff_dvd z).not.mpr hz))
    simpa using h5
  have h3 : ‖((z : ℚ_[l]) : PadicAlgCl l)‖ = 1 := by rw [PadicAlgCl.norm_extends]; exact h2
  have h4 : ‖(((z : ℚ_[l]) : PadicAlgCl l) : ℂ_[l])‖ = 1 := by rw [PadicComplex.norm_extends]; exact h3
  have e1 : (((z : ℚ_[l]) : PadicAlgCl l)) = (z : PadicAlgCl l) := map_intCast _ z
  have e2 : (((z : PadicAlgCl l)) : ℂ_[l]) = (z : ℂ_[l]) := by
    exact map_intCast (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) z
  have e3 : ((z : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ℂ_[l]) = (z : ℂ_[l]) := by simp
  show ‖((z : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1
  rw [e3, ← e2, ← e1]; exact h4

private theorem norm_add_le_max_maxUnramified_lemma (l : ℕ) [Fact l.Prime] (a b : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) :
    ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
  IsUltrametricDist.norm_add_le_max (a : ℂ_[l]) (b : ℂ_[l])

private theorem inv_prime_lt_one_lemma_2 (l : ℕ) (hl : 1 < l) : (l : ℝ)⁻¹ < 1 := by
  have hpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have h1 : (l : ℝ)⁻¹ * l = 1 := inv_mul_cancel₀ hpos.ne'
  have h2 : (1 : ℝ) < l := by exact_mod_cast hl
  nlinarith [inv_pos.2 hpos]

private theorem norm_frobenius_of_norm_eq_one_lemma_3 (l : ℕ) [Fact l.Prime]
    (σ : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l →+* Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) (hU : Formalism.L2.Th1.Top.FrP.UnrOK (Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) l σ)
    (u : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) (hu : ‖u‖ = 1) : ‖σ u‖ = 1 := by
  have hl2 : 2 < l := hU.2.1
  have hinv : (l : ℝ)⁻¹ < 1 := inv_prime_lt_one_lemma_2 l (by omega)
  have hc := hU.2.2.2.2 u hu.le
  have hul : ‖u ^ l‖ = 1 := by rw [norm_pow, hu, one_pow]
  apply le_antisymm
  · have h := norm_add_le_max_maxUnramified_lemma l (σ u - u ^ l) (u ^ l)
    rw [sub_add_cancel, hul] at h
    exact h.trans (max_le (hc.trans hinv.le) le_rfl)
  · have h := norm_add_le_max_maxUnramified_lemma l (σ u) (-(σ u - u ^ l))
    have e : σ u + -(σ u - u ^ l) = u ^ l := by ring
    rw [e, hul, norm_neg] at h
    by_contra hlt
    have := max_lt (not_le.mp hlt) (hc.trans_lt hinv)
    linarith

private theorem norm_frobenius_eq_lemma_4 (l : ℕ) [Fact l.Prime] (σ : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l →+* Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l)
    (hU : Formalism.L2.Th1.Top.FrP.UnrOK (Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) l σ) (x : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) : ‖σ x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨k, hk⟩ := hU.2.2.2.1 x hx
  have hl2 : 2 < l := hU.2.1
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hkpos : (0 : ℝ) < (l : ℝ) ^ k := zpow_pos hlpos k
  have hcn : ‖((l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k)‖ = ((l : ℝ) ^ k)⁻¹ := by
    rw [norm_zpow, hU.2.2.1, inv_zpow]
  have hσc : σ ((l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k) = (l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k := by
    rw [map_zpow₀, map_natCast]
  have hu : ‖x * (l : Formalism.L2.Th1.Top.FrP.MaximalUnramifiedExtension l) ^ k‖ = 1 := by
    rw [norm_mul, hk, hcn, mul_inv_cancel₀ hkpos.ne']
  have h := norm_frobenius_of_norm_eq_one_lemma_3 l σ hU _ hu
  rw [map_mul, hσc, norm_mul, hcn] at h
  rw [hk]
  exact mul_right_cancel₀ (inv_ne_zero hkpos.ne') (h.trans (mul_inv_cancel₀ hkpos.ne').symm)

theorem frob_isom (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hU : UnrOK (MaximalUnramifiedExtension l) l σ) (x : MaximalUnramifiedExtension l) :
    ‖σ x‖ = ‖x‖ :=
  norm_frobenius_eq_lemma_4 l σ hU x

theorem frob_conj (l : ℕ) [Fact l.Prime] (dK : ℕ) (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hU : UnrOK (MaximalUnramifiedExtension l) l σ)
    (δ : MaximalUnramifiedExtension l) (hδ2 : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : σ δ = -δ := by

  have hdvd : ¬ (l : ℤ) ∣ (-(dK : ℤ)) := by
    rw [dvd_neg]; exact_mod_cast hld
  have hcast : (((-(dK : ℤ)) : ℤ) : MaximalUnramifiedExtension l) = -(dK : MaximalUnramifiedExtension l) := by push_cast; ring
  have hδn : ‖δ‖ = 1 := by
    have h : ‖δ‖ ^ 2 = 1 := by rw [← norm_pow, hδ2, ← hcast, norm_int_Kur l _ hdvd]
    have h0 : 0 ≤ ‖δ‖ := norm_nonneg _
    nlinarith [h]
  obtain ⟨a, ha⟩ : ∃ a : ZMod l, a = (((-(dK : ℤ)) : ℤ) : ZMod l) := ⟨_, rfl⟩
  have ha' : a = -(dK : ZMod l) := by rw [ha]; push_cast; ring
  have ha0 : a ≠ 0 := by
    rw [ha]; intro h; exact hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h)
  have hsq : ¬ IsSquare a := by
    rintro ⟨b, hb⟩
    exact hin ⟨b, by rw [pow_two, ← hb, ha']⟩
  have hpow : a ^ (l / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one l ha0 with h | h
    · exact absurd ((ZMod.euler_criterion l ha0).mpr h) hsq
    · exact h
  have hpow' : (-(dK : ZMod l)) ^ (l / 2) = -1 := by rw [← ha']; exact hpow
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = 1 - (-(dK : ℤ)) ^ (l / 2) := ⟨_, rfl⟩
  have hcnd : ¬ (l : ℤ) ∣ c := by
    intro hdc
    have h0 : ((c : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c l).mpr hdc
    have h2 : ((c : ℤ) : ZMod l) = ((2 : ℤ) : ZMod l) := by
      rw [hc]; push_cast; rw [hpow']; ring
    rw [h2] at h0
    have := Int.le_of_dvd two_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 l).mp h0)
    omega
  have hodd : l = 2 * (l / 2) + 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : l.Prime).odd_of_ne_two (by omega)
    omega
  have hpowl : δ ^ l = δ * (((-(dK : ℤ)) ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l) := by
    have e : δ ^ l = δ ^ (2 * (l / 2) + 1) := by rw [← hodd]
    rw [e, pow_succ, pow_mul, hδ2]; push_cast; ring
  have hsq2 : (σ δ - δ) * (σ δ + δ) = 0 := by
    have h : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ2, map_neg, map_natCast]
    linear_combination h
  rcases mul_eq_zero.mp hsq2 with h | h
  · exfalso
    have hσ : σ δ = δ := sub_eq_zero.mp h
    have hb := hU.2.2.2.2 δ hδn.le
    rw [hσ, hpowl] at hb
    have e : δ - δ * (((-(dK : ℤ)) ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l) = δ * ((c : ℤ) : MaximalUnramifiedExtension l) := by
      rw [hc]; push_cast; ring
    rw [e, norm_mul, hδn, norm_int_Kur l c hcnd, one_mul] at hb
    have hinv : (l : ℝ)⁻¹ < 1 := inv_prime_lt_one_lemma_2 l (by omega)
    linarith
  · exact eq_neg_of_add_eq_zero_left h

theorem frobStep : FrobStep := by
  intro l hl dK hl5 hld hd hd8 hin ι σ hU
  refine ⟨frob_isom l σ hU, ?_⟩
  have hmem := delta_mem l dK hd (by omega) hld ι
  refine ⟨⟨ι (sq dK), hmem⟩, rfl, ?_⟩
  apply frob_conj l dK hl5 hld hin σ hU
  have hsqc : (ι (sq dK)) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow, sq_sq, map_neg, map_natCast]
  apply Subtype.ext
  simpa using hsqc

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
