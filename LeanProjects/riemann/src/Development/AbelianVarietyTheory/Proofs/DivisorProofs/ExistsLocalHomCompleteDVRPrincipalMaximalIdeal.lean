import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrInjectiveLocal
open IsLocalRing

namespace GlobalTheory.PrincDvr

def powInf {B : Type} [CommRing B] (ϖ : B) : Ideal B := ⨅ n : ℕ, Ideal.span {ϖ ^ n}

variable {B : Type} [CommRing B] [IsLocalRing B] {ϖ : B}

theorem pow_not_mem_span_succ (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) (n : ℕ) :
    ϖ ^ n ∉ Ideal.span {ϖ ^ (n + 1)} := by
  intro h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  have hn : ϖ ^ n ∈ nonZeroDivisors B := pow_mem hϖ n
  have e : (b * ϖ - 1) * ϖ ^ n = 0 := by linear_combination hb
  have e1 : b * ϖ - 1 = 0 := (mem_nonZeroDivisors_iff.1 hn).2 _ e
  have hmem : ϖ ∈ maximalIdeal B := by rw [hm]; exact Ideal.mem_span_singleton_self ϖ
  exact (mem_maximalIdeal _).1 hmem (isUnit_iff_exists_inv.2 ⟨b, by rw [mul_comm]; exact sub_eq_zero.1 e1⟩)

theorem exists_unit_mul_pow (hm : maximalIdeal B = Ideal.span {ϖ}) (x : B) (hx : x ∉ powInf ϖ) :
    ∃ (n : ℕ) (u : Bˣ), x = u * ϖ ^ n := by
  classical
  have hex : ∃ n, ¬ ϖ ^ n ∣ x := by
    by_contra h
    push_neg at h
    exact hx (Ideal.mem_iInf.2 fun n => Ideal.mem_span_singleton.2 (h n))
  obtain ⟨N, hN, hmin⟩ : ∃ N, ¬ ϖ ^ N ∣ x ∧ ∀ m < N, ϖ ^ m ∣ x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.1 (Nat.find_min hex hm)⟩
  clear hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero]; exact one_dvd x
  obtain ⟨u, hu⟩ : ϖ ^ (N - 1) ∣ x := hmin _ (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
  have hu' : IsUnit u := by
    by_contra hu'
    have hmem : u ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal u).2 hu'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    apply hN
    refine ⟨c, ?_⟩
    rw [hu, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
  exact ⟨N - 1, hu'.unit, by rw [hu, IsUnit.unit_spec, mul_comm]⟩

theorem isPrime_powInf (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) :
    (powInf ϖ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using Ideal.mem_iInf.1 h 1)
  · intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨m, u, rfl⟩ := exists_unit_mul_pow hm a h.1
    obtain ⟨k, v, rfl⟩ := exists_unit_mul_pow hm b h.2
    have hmem := Ideal.mem_iInf.1 hab (m + k + 1)
    apply pow_not_mem_span_succ hm hϖ (m + k)
    have e1 : (u : B) * ϖ ^ m * (v * ϖ ^ k) = ((u * v : Bˣ) : B) * ϖ ^ (m + k) := by push_cast; ring
    have e : ϖ ^ (m + k) = (((u * v)⁻¹ : Bˣ) : B) * ((u : B) * ϖ ^ m * (v * ϖ ^ k)) := by
      rw [e1, Units.inv_mul_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ hmem

theorem exists_cDvr_localHom : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} →
    ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  intro B _ _ ϖ hm hϖ h0
  haveI := isPrime_powInf hm hϖ
  have hp0 : Ideal.Quotient.mk (powInf ϖ) ϖ ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    exact pow_not_mem_span_succ hm hϖ 1 (by simpa using Ideal.mem_iInf.1 h 2)
  have hnu : ∀ a : B, ¬ IsUnit a → ∃ c, Ideal.Quotient.mk (powInf ϖ) a =
      Ideal.Quotient.mk (powInf ϖ) ϖ * Ideal.Quotient.mk (powInf ϖ) c := by
    intro a ha
    have hmem : a ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal a).2 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, map_mul, mul_comm]⟩
  have hpu : ¬ IsUnit (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w⁻¹ : (B ⧸ powInf ϖ)ˣ).val
    have e : Ideal.Quotient.mk (powInf ϖ) (ϖ * c) = Ideal.Quotient.mk (powInf ϖ) 1 := by
      rw [map_mul, hc, ← hw, Units.mul_inv, map_one]
    have h1 := Ideal.mem_iInf.1 (Ideal.Quotient.eq.1 e) 1
    rw [pow_one] at h1
    have h2 : (1 : B) ∈ Ideal.span {ϖ} := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self ϖ)) h1
      simpa using this
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using h2)
  have hirr : Irreducible (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    refine irreducible_iff.2 ⟨hpu, fun a b hab => ?_⟩
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases ha : IsUnit a'
    · exact Or.inl (ha.map _)
    · obtain ⟨c, hc⟩ := hnu a' ha
      right
      rw [hc, mul_assoc] at hab
      have e := mul_left_cancel₀ hp0 ((mul_one _).trans hab)
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e.symm⟩
  have hfac : ∀ {x : B ⧸ powInf ϖ}, x ≠ 0 → ∃ n, Associated (Ideal.Quotient.mk (powInf ϖ) ϖ ^ n) x := by
    intro x hx
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x' ∉ powInf ϖ := fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h)
    obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow hm x' hx'
    refine ⟨n, Units.map (Ideal.Quotient.mk (powInf ϖ)).toMonoidHom u, ?_⟩
    simp only [map_mul, map_pow, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  haveI : IsDiscreteValuationRing (B ⧸ powInf ϖ) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, hfac⟩
  have hle : powInf ϖ ≤ RingHom.ker (residue B) := by
    intro a ha
    rw [RingHom.mem_ker, residue_eq_zero_iff, hm]
    simpa using Ideal.mem_iInf.1 ha 1
  have hc0 : CharZero (B ⧸ powInf ϖ) := RingHom.charZero (Ideal.Quotient.lift (powInf ϖ) (residue B) hle)
  have hloc : IsLocalHom (Ideal.Quotient.mk (powInf ϖ)) := ⟨fun a ha => by
    by_contra h
    obtain ⟨c, hc⟩ := hnu a h
    rw [hc] at ha
    exact hpu (isUnit_of_mul_isUnit_left ha)⟩
  obtain ⟨W, _, _, _, g, hW, hinj, hg⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding (B ⧸ powInf ϖ) inferInstance
    inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) hc0
  refine ⟨W, inferInstance, inferInstance, inferInstance, g.comp (Ideal.Quotient.mk (powInf ϖ)), hW, ?_, ?_⟩
  · haveI := hloc; haveI := hg; infer_instance
  · intro h
    exact hp0 (hinj (by rw [map_zero]; exact h))

end GlobalTheory.PrincDvr
