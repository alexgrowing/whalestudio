import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem absNorm_span_modEq_one {F : Type} [Field F] [NumberField F] (l m : ℕ) {a : 𝓞 F} (ha : a ≠ 0)
    (ha1 : a - 1 ∈ powMod F l m) (hpos : ∀ σ : F →+* ℝ, 0 < σ (a : F)) :
    Ideal.absNorm (Ideal.span {a}) ≡ 1 [MOD l ^ m] := by
  have hn : 0 < Algebra.norm ℤ a := by
    have h := GlobalTheory.RayRootOfUnity.norm_pos_of_pos_real (x := (a : F)) (by simpa using ha) hpos
    rw [← Algebra.coe_norm_int] at h
    exact_mod_cast h
  have hc := GlobalTheory.Mem.RayNorm.norm_cast_eq F (l ^ m) (x := a) (y := 1) (by
    have e : ((l ^ m : ℕ) : 𝓞 F) = (l : 𝓞 F) ^ m := by push_cast; rfl
    rw [e]
    exact ha1)
  rw [map_one, Int.cast_one] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod (l ^ m)) (Int.natAbs_of_nonneg hn.le)
  rw [Int.cast_natCast] at h2
  rw [← ZMod.natCast_eq_natCast_iff, Ideal.absNorm_span_singleton, h2, hc, Nat.cast_one]

theorem absNorm_modEq_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)),
    RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  intro F _ _ l m I J h
  obtain ⟨a, b, ha, hb, ha1, hb1, hσ, he⟩ := h
  have h1 := absNorm_span_modEq_one l m ha ha1 fun σ => (hσ σ).1
  have h2 := absNorm_span_modEq_one l m hb hb1 fun σ => (hσ σ).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD l ^ m] := h1.symm.mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD l ^ m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

end GlobalTheory.CompanionTheory.RayFacts
