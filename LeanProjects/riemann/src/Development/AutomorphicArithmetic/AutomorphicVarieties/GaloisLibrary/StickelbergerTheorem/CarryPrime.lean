import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Jacobi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Sqfree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.carryPrime :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p), p.Coprime M →
    ∀ v : HeightOneSpectrum (𝓞 K), RingHom.ker π = v.asIdeal → ∀ a b : ZMod M,
    ∏ t : (ZMod M)ˣ, clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) ^ carry M (a * t) (b * t) = 1 := by
  intro M _ K _ _ _ p _ π hp v hv a b
  classical
  have hprod : ∀ s : Finset (ZMod M)ˣ, (∏ t ∈ s, conjI M K (RingHom.ker π) t).IsPrincipal →
      ∏ t ∈ s, clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) = 1 := by
    intro s hs
    unfold primeCl
    simp only [class_map_mk0]
    rw [← map_prod, ClassGroup.mk0_eq_one_iff, Submonoid.coe_finset_prod]
    simp only [idMap_inv]
    rw [← hv]
    exact hs
  have hall : ∏ t, clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) = 1 := by
    apply hprod
    rw [(splitProd M K p π hp).2]
    exact ⟨⟨_, rfl⟩⟩
  have hterm : ∀ t : (ZMod M)ˣ, clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) ^ carry M (a * t) (b * t)
      = if M ≤ (a * t).val + (b * t).val then clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) else 1 := by
    intro t
    unfold carry
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun t _ => hterm t), ← Finset.prod_filter]
  by_cases ha : a = 0
  · have h0 : ∀ t ∈ (Finset.univ : Finset (ZMod M)ˣ), ¬ (M ≤ (a * t).val + (b * t).val) := by
      intro t _
      rw [ha, zero_mul, ZMod.val_zero, zero_add, not_le]
      exact ZMod.val_lt _
    rw [Finset.filter_false_of_mem h0, Finset.prod_empty]
  by_cases hb : b = 0
  · have h0 : ∀ t ∈ (Finset.univ : Finset (ZMod M)ˣ), ¬ (M ≤ (a * t).val + (b * t).val) := by
      intro t _
      rw [hb, zero_mul, ZMod.val_zero, add_zero, not_le]
      exact ZMod.val_lt _
    rw [Finset.filter_false_of_mem h0, Finset.prod_empty]
  by_cases hab : a + b = 0
  · have hb' : b = -a := eq_neg_of_add_eq_zero_right hab
    have h1 : ∀ t ∈ (Finset.univ : Finset (ZMod M)ˣ), M ≤ (a * t).val + (b * t).val := by
      intro t _
      have hat : a * (t : ZMod M) ≠ 0 := by
        intro h
        apply ha
        simpa using congrArg (· * ((t⁻¹ : (ZMod M)ˣ) : ZMod M)) h
      have hlt := ZMod.val_lt (a * (t : ZMod M))
      rw [hb', neg_mul, ZMod.neg_val, if_neg hat]
      omega
    rw [Finset.filter_true_of_mem h1]
    exact hall
  obtain ⟨J, hJ, hJt⟩ := jacobi M K p π hp a b ha hb hab
  have hsp := sqfree (𝓞 K) (ZMod M)ˣ (conjI M K (RingHom.ker π)) (splitInj M K p π hp)
    (splitProd M K p π hp).1 J (Finset.univ.filter fun t => ¬ (M ≤ (a * t).val + (b * t).val)) ?_ ?_
  · have hnot : ∏ t ∈ Finset.univ.filter (fun t : (ZMod M)ˣ => ¬ (M ≤ (a * t).val + (b * t).val)),
        clMap (sg M K t)⁻¹.toRingEquiv (primeCl v) = 1 := by
      apply hprod
      rw [← hsp]
      exact ⟨⟨J, rfl⟩⟩
    have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun t : (ZMod M)ˣ => M ≤ (a * t).val + (b * t).val)
      (fun t => clMap (sg M K t)⁻¹.toRingEquiv (primeCl v))
    rw [hnot, mul_one, hall] at hsplit
    exact hsplit
  · rw [(splitProd M K p π hp).2, Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
    exact hJ
  · intro t
    rw [Finset.mem_filter, hJt t]
    unfold carry
    split_ifs with h <;> simp [h]
