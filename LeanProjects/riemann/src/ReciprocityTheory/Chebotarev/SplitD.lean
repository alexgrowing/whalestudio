import ReciprocityTheory.Chebotarev.SplitDef

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitD_natCast_not_mem (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (hl : ¬ l ∣ Nrm q) : (l : 𝓞 E) ∉ q.asIdeal := by
  intro h
  have hmax : q.asIdeal.IsMaximal := q.isMaximal
  let : Field (𝓞 E ⧸ q.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 E ⧸ q.asIdeal) := by
    have := (Ideal.absNorm_ne_zero_iff q.asIdeal).1 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
    exact this
  let := Fintype.ofFinite (𝓞 E ⧸ q.asIdeal)
  have h0 : ((l : 𝓞 E ⧸ q.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact h
  set p := ringChar (𝓞 E ⧸ q.asIdeal)
  have hpl : p ∣ l := (ringChar.spec _ l).1 h0
  have hp1 : p ≠ 1 := CharP.ringChar_ne_one
  have hpeq : p = l := ((Fact.out : l.Prime).eq_one_or_self_of_dvd p hpl).resolve_left hp1
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) p
  apply hl
  have : Nrm q = Fintype.card (𝓞 E ⧸ q.asIdeal) := by
    rw [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [this, hn, hpeq]
  exact dvd_pow_self l n.ne_zero

theorem splitD_frob (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    ∃ σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E,
      σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
        IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ Nrm q ∧
      ∀ x : 𝓞 (CyclotomicField l E), ∃ y : 𝓞 (CyclotomicField l E),
        (y : CyclotomicField l E) = σ (x : CyclotomicField l E) ∧ y - x ^ Nrm q ∈ P.asIdeal := by
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : Algebra.IsInvariant (𝓞 E) (𝓞 (CyclotomicField l E))
      (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Algebra.isInvariant_of_isGalois' (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))
  have : Finite (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Finite.of_equiv _ (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).toEquiv
  have : P.asIdeal.IsPrime := P.isPrime
  have : Finite (𝓞 (CyclotomicField l E) ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff P.asIdeal).1 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E)
    (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) P.asIdeal
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) = Nrm q := by
    rw [Nrm, ← hP, under_asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ : ∀ x : 𝓞 (CyclotomicField l E),
      ((τ x : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
        (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ
          (x : CyclotomicField l E) := by
    intro x
    have := algebraMap_galRestrict_apply (𝓞 E)
      ((galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ) x
    simpa only [MulEquiv.apply_symm_apply] using this
  have hfr : ∀ x : 𝓞 (CyclotomicField l E), τ x - x ^ Nrm q ∈ P.asIdeal := by
    intro x
    have := hτ x
    rw [hcard] at this
    exact this
  refine ⟨(galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ, ?_,
    fun x => ⟨τ x, hσ x, hfr x⟩⟩
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hlP : ((l : ℕ) : 𝓞 (CyclotomicField l E)) ∉ P.asIdeal := by
    intro h
    apply splitD_natCast_not_mem E l q hl
    rw [← hP, under_asIdeal, Ideal.mem_comap, map_natCast]
    exact h
  have h1 := hτ.apply_of_pow_eq_one (ζ := hz.toInteger) (m := l) hz.toInteger_isPrimitiveRoot.pow_eq_one hlP
  rw [hcard] at h1
  have h2 : ((τ hz.toInteger : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
      ((hz.toInteger ^ Nrm q : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) := congrArg _ h1
  rw [hσ] at h2
  push_cast at h2
  exact h2

end ReciprocityTheory.Cheb
