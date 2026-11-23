import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.splitInj :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p), p.Coprime M →
    Function.Injective (conjI M K (RingHom.ker π)) := by
  intro M _ K _ _ _ p _ π hp a b hab
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπz, -⟩ := redRoot (𝓞 K) p π M _ hp hz
  have key : ∀ x : 𝓞 K, π (sgO M K a x) = π (sgO M K b x) := by
    intro x
    have h1 : x - ((π (sgO M K a x)).val : 𝓞 K) ∈ conjI M K (RingHom.ker π) a := by
      simp only [conjI, Ideal.mem_comap, RingHom.mem_ker, map_sub, map_natCast,
        ZMod.natCast_zmod_val, sub_self]
    rw [hab] at h1
    simp only [conjI, Ideal.mem_comap, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_eq_zero] at h1
    exact h1.symm
  have h2 := key (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger
  rw [sgO_apply _ _ _ hz.pow_eq_one, sgO_apply _ _ _ hz.pow_eq_one, map_pow, map_pow] at h2
  exact Units.ext (ZMod.val_injective _ (hπz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2))
