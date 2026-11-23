import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.red :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)),
    (Ideal.absNorm P = p → ∃ π : 𝓞 K →+* ZMod p, RingHom.ker π = P) ∧
    ∀ π : 𝓞 K →+* ZMod p, RingHom.ker π = P → Ideal.absNorm P = p ∧ P.IsMaximal ∧ Prime P ∧ (p : 𝓞 K) ∈ P := by
  intro K _ _ p hp P
  have hpp : p.Prime := hp.out
  have hcard : ∀ π : 𝓞 K →+* ZMod p, Function.Surjective π := fun π x => by
    refine ⟨(x.val : 𝓞 K), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  refine ⟨fun h => ?_, fun π hπ => ?_⟩
  · have hfin : Finite (𝓞 K ⧸ P) := by
      rw [← Ideal.absNorm_ne_zero_iff, h]
      exact hpp.ne_zero
    let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    have hc : Fintype.card (𝓞 K ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h]
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hpp hc
    refine ⟨(e.symm : (𝓞 K ⧸ P) →+* ZMod p).comp (Ideal.Quotient.mk P), ?_⟩
    rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]
  · have hs := hcard π
    have e : (𝓞 K ⧸ P) ≃+* ZMod p := hπ ▸ RingHom.quotientKerEquivOfSurjective hs
    have hn : Ideal.absNorm P = p := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv, Nat.card_zmod]
    have hmax : P.IsMaximal := hπ ▸ RingHom.ker_isMaximal_of_surjective π hs
    refine ⟨hn, hmax, ?_, ?_⟩
    · refine Ideal.prime_of_isPrime ?_ hmax.isPrime
      rintro rfl
      rw [Ideal.absNorm_bot] at hn
      exact hpp.ne_zero hn.symm
    · rw [← hπ, RingHom.mem_ker, map_natCast, ZMod.natCast_self]
