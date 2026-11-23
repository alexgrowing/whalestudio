import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame

open NumberField IsDedekindDomain GlobalTheory.ShFam.Pad

namespace GlobalTheory.PlaceSum

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_eq_iff (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    resP v = p ↔ ((p : 𝓞 F) ∈ v.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  unfold resP
  constructor
  · intro h
    have h0 : ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := ringChar.Nat.cast_ringChar
    rw [h, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  · intro h
    have h0 : (Ideal.Quotient.mk v.asIdeal (p : 𝓞 F)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [map_natCast] at h0
    have hd : ringChar (𝓞 F ⧸ v.asIdeal) ∣ p := ringChar.dvd h0
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
    · exact h1

theorem finprod_adicAbv {z : F} (hz : z ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v z =
      |((Algebra.norm ℚ z : ℚ) : ℝ)|⁻¹ := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z) =
      (fun w : FinitePlace F => w z) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext v
    simp [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  refine ⟨?_, ?_⟩
  · rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      FinitePlace.equivHeightOneSpectrum.symm.injective.injOn
  · rw [hfun]
    refine (finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm
      (f := fun w : FinitePlace F => w z)).trans ?_
    rw [FinitePlace.prod_eq_inv_abs_norm hz]
    push_cast; rfl

theorem adicAbv_natCast_ne_one_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    HeightOneSpectrum.adicAbv F v (n : F) ≠ 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have e : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := (map_natCast _ n).symm
  rw [e, Ne, ← not_not (a := (n : 𝓞 F) ∈ v.asIdeal)]
  exact not_congr (v.adicAbv_coe_eq_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _)

theorem finite_mulSupport_adicAbv_natCast {p : ℕ} (hp : p.Prime) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v (p : F)).Finite :=
  (finprod_adicAbv (z := (p : F)) (by exact_mod_cast hp.ne_zero)).1

theorem mem_finite_residueChar_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset ↔ resP v = p := by
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, adicAbv_natCast_ne_one_iff, residueCharacteristic_eq_iff v hp]

theorem sum_localDeg_eq {p : ℕ} (hp : p.Prime) :
    ∑ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset,
      -Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p = (Module.finrank ℚ F : ℝ) := by
  have hp0 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hfin, hprod⟩ := finprod_adicAbv (F := F) hp0
  rw [finprod_eq_prod _ hfin] at hprod
  have hN : Algebra.norm ℚ (p : F) = (p : ℚ) ^ Module.finrank ℚ F := by
    rw [← map_natCast (algebraMap ℚ F) p, Algebra.norm_algebraMap]
  rw [hN] at hprod
  push_cast at hprod
  have hne : ∀ v ∈ hfin.toFinset, HeightOneSpectrum.adicAbv F v (p : F) ≠ 0 :=
    fun v _ => (AbsoluteValue.ne_zero_iff _).2 hp0
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod hne, abs_of_nonneg (by positivity), Real.log_inv, Real.log_pow] at hlog
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hlog, neg_neg, mul_div_assoc, div_self hlp.ne', mul_one]

theorem sum_localDeg_le : ∀ {F : Type} [Field F] [NumberField F] (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p) →
    (∀ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) ≤ 1) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∈ S ↔ resP v ∈ T) ∧
      ∑ v ∈ S, (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) ≤
        (Module.finrank ℚ F : ℝ) * ∑ p ∈ T, g p := by
  intro F _ _ T hT g _
  classical
  refine ⟨fun v => HeightOneSpectrum.adicAbv_natCast_le_one F v _, ?_⟩
  let Sp : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun p =>
    if h : p.Prime then (finite_mulSupport_adicAbv_natCast (F := F) h).toFinset else ∅
  have hSp : ∀ p ∈ T, ∀ v, v ∈ Sp p ↔ resP v = p := by
    intro p hpT v
    simp only [Sp, dif_pos (hT p hpT)]
    exact mem_finite_residueChar_eq (hT p hpT) v
  let S := T.biUnion Sp
  have hS : ∀ v, v ∈ S ↔ resP v ∈ T := by
    intro v
    simp only [S, Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hpT, hv⟩
      rw [(hSp p hpT v).1 hv]; exact hpT
    · intro h
      exact ⟨resP v, h, (hSp _ h v).2 rfl⟩
  refine ⟨S, hS, le_of_eq ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := resP) (t := T) (fun v hv => (hS v).1 hv), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hpT => ?_
  have hfib : S.filter (fun v => resP v = p) = (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset := by
    ext v
    rw [Finset.mem_filter, mem_finite_residueChar_eq (hT p hpT), hS]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hpT, h⟩
  rw [hfib]
  have hc : ∀ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset,
      (-Real.log (HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) =
        (-Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p) * g p := by
    intro v hv
    rw [(mem_finite_residueChar_eq (hT p hpT) v).1 hv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, sum_localDeg_eq (hT p hpT), mul_comm]

end GlobalTheory.PlaceSum
