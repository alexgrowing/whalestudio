import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.jacDvd :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (p : ℕ) [Fact p.Prime] (χ φ : MulChar (ZMod p) R),
    χ ≠ 1 → φ ≠ 1 → χ * φ ≠ 1 → jacobiSum χ φ ∣ (p : R) := by
  intro R _ _ _ p _ χ φ hχ hφ hχφ
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have : CharZero K := charZero_of_injective_algebraMap hf
  have hc : ringChar K ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).ne_zero.symm
  have h1 : χ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hχ
  have h2 : φ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hφ
  have h3 : χ.ringHomComp f * φ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr hχφ
  have key := jacobiSum_mul_jacobiSum_inv hc h1 h2 h3
  rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp, ← map_mul, ZMod.card, ← map_natCast f] at key
  exact ⟨_, (hf key).symm⟩
