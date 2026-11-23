import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def levCongr {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) (c : O) : Lev M c ≃ Lev N c where
  toFun x := Lev.mk (e x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  invFun y := Lev.mk (e.symm y.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  left_inv x := Lev.ext (by simp [Lev.val_mk])
  right_inv y := Lev.ext (by simp [Lev.val_mk])

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def divPowQ (ϖ : O) (n : ℕ) : O →ₗ[O] Formalism.NG.KO O :=
  (1 : Submodule O (FractionRing O)).mkQ ∘ₗ
    LinearMap.mulLeft O ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹) ∘ₗ
      Algebra.linearMap O (FractionRing O)

theorem divPowQ_apply (ϖ : O) (n : ℕ) (a : O) :
    divPowQ ϖ n a = Submodule.Quotient.mk
      ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem ker_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.ker (divPowQ ϖ n) = Ideal.span {ϖ ^ n} := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext a
  rw [LinearMap.mem_ker, divPowQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [map_mul, map_pow, hb, mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, mul_comm (algebraMap O (FractionRing O) b), ← mul_assoc,
      inv_mul_cancel₀ hπ, one_mul]

theorem range_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.range (divPowQ ϖ n) = LinearMap.ker ((ϖ ^ n) • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O) := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [divPowQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one, Algebra.smul_def, map_pow, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact ⟨a, rfl⟩
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
      Algebra.smul_def, map_pow] at hy
    obtain ⟨b, hb⟩ := hy
    refine ⟨b, ?_⟩
    rw [divPowQ_apply, hb, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem natCard_lev_KO {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (O ⧸ Ideal.span {ϖ ^ n}) := by
  have h1 : Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (LinearMap.range (divPowQ ϖ n)) := by
    rw [range_divPowQ hϖ n]; rfl
  rw [h1, ← Nat.card_congr (LinearMap.quotKerEquivRange (divPowQ ϖ n)).toEquiv, ker_divPowQ hϖ n]

theorem natCard_quot_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {ϖ ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := n)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [hq, ← hϖ.maximalIdeal_eq]
  rfl

theorem lev_pow_card {ϖ : O} (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (e : M ≃ₗ[O] Formalism.NG.KO O) (n : ℕ) [Finite (IsLocalRing.ResidueField O)] :
    Finite (Lev M (ϖ ^ n)) ∧
      Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hc : Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
    rw [Nat.card_congr (levCongr e (ϖ ^ n)), natCard_lev_KO hϖ.ne_zero, natCard_quot_pow hϖ]
  refine ⟨Nat.finite_of_card_ne_zero ?_, hc⟩
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DVR

theorem levKO_card : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  fun hϖ _ _ _ e n => lev_pow_card hϖ e n

end GlobalTheory.ShapeNeg
