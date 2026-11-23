import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar partialLFunction)

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinEuler

open Classical in

def partialTerm (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) : Ideal (𝓞 ℚ) →* ℂ where
  toFun I := if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0
  map_one' := by
    have h : ∀ v ∈ S, ¬ v.asIdeal ∣ (1 : Ideal (𝓞 ℚ)) := fun v _ hv =>
      v.isPrime.ne_top (Ideal.isUnit_iff.1 (isUnit_of_dvd_one hv))
    rw [if_pos h, map_one]
  map_mul' I J := by
    have hp : ∀ v : Pl, v.asIdeal ∣ I * J ↔ v.asIdeal ∣ I ∨ v.asIdeal ∣ J := fun v =>
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).dvd_mul
    by_cases hI : ∀ v ∈ S, ¬ v.asIdeal ∣ I
    · by_cases hJ : ∀ v ∈ S, ¬ v.asIdeal ∣ J
      · have hIJ : ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun v hv h =>
          ((hp v).1 h).elim (hI v hv) (hJ v hv)
        rw [if_pos hIJ, if_pos hI, if_pos hJ, map_mul]
      · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
          hJ fun v hv hd => h v hv ((hp v).2 (Or.inr hd))
        rw [if_neg hIJ, if_neg hJ, mul_zero]
    · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
        hI fun v hv hd => h v hv ((hp v).2 (Or.inl hd))
      rw [if_neg hIJ, if_neg hI, zero_mul]

open Classical in
theorem partialTerm_apply (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) (I : Ideal (𝓞 ℚ)) :
    partialTerm c S s I = if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0 :=
  rfl

theorem norm_partialTerm_le (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) (I : Ideal (𝓞 ℚ)) :
    ‖partialTerm c S s I‖ ≤ ‖c.coeffTerm s I‖ := by
  rw [partialTerm_apply]
  split_ifs
  · exact le_rfl
  · simp

theorem partialTerm_bot (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) :
    partialTerm c S s ⊥ = 0 := by
  have h := norm_partialTerm_le c S s ⊥
  rw [c.coeffTerm_bot, norm_zero] at h
  exact norm_le_zero_iff.1 h

theorem tsum_partialTerm (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) :
    ∑' I, partialTerm c S s I = partialLFunction c S s := by
  rw [partialLFunction]
  refine tsum_congr fun I => ?_
  rw [partialTerm_apply, HeckeCharacter.coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]
  split_ifs
  · rfl
  · simp

theorem valued_unifUnit (v : Pl) :
    Valued.v ((unifUnit (Qv v) : (Qv v)ˣ) : Qv v) = WithZero.exp (-1 : ℤ) := by
  rw [valued_eq_exp_neg_ord (unifUnit (Qv v)).ne_zero, ord_unifUnit]

theorem localLFactor_eq (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) {v : Pl} (hv : v ∉ S)
    (hu : IsUnramifiedChar (localChar c v)) :
    localLFactor (localChar c v) s = (1 - partialTerm c S s v.asIdeal)⁻¹ := by
  have hnd : ¬ v.asIdeal ∣ c.conductor := (c.isUnramifiedChar_localChar_iff v).1 hu
  have hS : ∀ w ∈ S, ¬ w.asIdeal ∣ v.asIdeal := fun w hw h =>
    hv (heightOneSpectrum_eq_of_dvd h ▸ hw)
  rw [localLFactor_of_isUnramified hu, partialTerm_apply, if_pos hS,
    HeckeCharacter.coeffTerm_apply, c.coeff_asIdeal_eq_toIdele hnd (valued_unifUnit v),
    residueCard_adicCompletion, Complex.cpow_neg, div_eq_mul_inv]
  rfl

theorem hasProd_partial (c : HeckeCharacter ℚ) (S : Finset Pl) {s : ℂ} (hs : 1 < s.re)
    (hun : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) :
    HasProd (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s)
      (partialLFunction c S s) := by
  have hsum : Summable fun I => ‖partialTerm c S s I‖ :=
    (c.summable_norm_coeffTerm hs).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_partialTerm_le c S s)
  have h := hasProd_euler (partialTerm c S s) hsum (partialTerm_bot c S s)
  rw [tsum_partialTerm] at h
  rw [← hasProd_subtype_iff_of_mulSupport_subset (s := {v : Pl | v ∉ S})] at h
  · have hfun : (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s) =
        fun v : {v : Pl // v ∉ S} => (1 - partialTerm c S s v.1.asIdeal)⁻¹ :=
      funext fun v => localLFactor_eq c S s v.2 (hun v.1 v.2)
    rw [hfun]
    exact h
  · intro v hv
    by_contra hvS
    have hvS' : v ∈ S := by simpa using hvS
    apply hv
    have h0 : partialTerm c S s v.asIdeal = 0 := by
      rw [partialTerm_apply, if_neg fun h => h v hvS' dvd_rfl]
    simp [h0]

theorem norm_localLFactor_sub_one_le {s : ℂ} (hs : 1 < s.re) {v : Pl} {ν : (Qv v)ˣ →* ℂˣ}
    (hν : IsUnit1 ν) :
    ‖localLFactor ν s - 1‖ ≤ 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ s.re)⁻¹ := by
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← residueCard_adicCompletion]
    exact_mod_cast one_lt_residueCard (K := Qv v)
  have hqpos : 0 < Ideal.absNorm v.asIdeal := by
    have : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
    exact_mod_cast this
  set t : ℝ := ((Ideal.absNorm v.asIdeal : ℝ) ^ s.re)⁻¹ with ht
  have htpos : 0 < t := inv_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
  by_cases hu : IsUnramifiedChar ν
  · rw [localLFactor_of_isUnramified hu, residueCard_adicCompletion]
    set x : ℂ := ((ν (unifUnit (Qv v)) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hx
    have hxn : ‖x‖ = t := by
      rw [hx, norm_mul, hν.2, one_mul, Complex.norm_natCast_cpow_of_pos hqpos, Complex.neg_re,
        Real.rpow_neg (by linarith)]
    have hthalf : t ≤ 1 / 2 := by
      rw [ht, one_div]
      refine inv_anti₀ (by norm_num) ?_
      calc (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := hq2
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    have h1 : (1 : ℝ) / 2 ≤ ‖1 - x‖ := by
      have := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one, hxn] at this
      linarith
    have hne : 1 - x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      norm_num at h1
    have he : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
      field_simp
      ring
    rw [he, norm_mul, norm_inv, hxn, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ htpos.le
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  · rw [localLFactor_of_not_isUnramified hu, sub_self, norm_zero]
    positivity

theorem multipliable_local (S : Finset Pl) {s : ℂ} (hs : 1 < s.re) (ν : ∀ v : Pl, (Qv v)ˣ →* ℂˣ)
    (hν : ∀ v, IsUnit1 (ν v)) :
    Multipliable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s := by
  have hinj : Function.Injective fun v : {v : Pl // v ∉ S} => v.1.asIdeal :=
    fun v w h => Subtype.ext (HeightOneSpectrum.ext h)
  have hb : Summable fun v : {v : Pl // v ∉ S} =>
      2 * ((Ideal.absNorm v.1.asIdeal : ℝ) ^ s.re)⁻¹ :=
    ((summable_absNorm_rpow_inv (K := ℚ) hs).comp_injective hinj).mul_left 2
  have hf : Summable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s - 1 :=
    Summable.of_norm_bounded hb fun v => norm_localLFactor_sub_one_le hs (hν v.1)
  simpa using Complex.multipliable_one_add_of_summable hf

theorem e2 (_ : Ad3.R.B0) : Ad3.R.E2 := by
  intro S s hs
  refine ⟨fun c hc => ⟨fun v hv => ?_, hasProd_partial c S hs hc⟩,
    fun ν hν => multipliable_local S hs ν hν⟩
  by_contra hvS
  exact (c.isUnramifiedChar_localChar_iff v).1 (hc v hvS) hv

end GlobalTheory.CompanionTheory.RankinEuler

end
