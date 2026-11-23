import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerExt

theorem exists_extend_of_formallySmooth {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r, D' (algebraMap R S r) = algebraMap R S (D r) := by
  let g : R →+* TrivSqZeroExt S S :=
    { toFun := fun r ↦ TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r))
      map_one' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_one,
            map_one, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one,
            Derivation.map_one_eq_zero, map_zero, zero_add]
      map_mul' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul,
            map_mul, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, Derivation.leibniz,
            smul_eq_mul, map_add, map_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, zero_add, add_zero]
          ring
      map_zero' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero,
            map_zero, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero,
            map_zero, zero_add]
      map_add' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, map_add, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add, zero_add] }
  have hg : ∀ r, (g r).fst = algebraMap R S r ∧ (g r).snd = algebraMap R S (D r) := fun r ↦ by
    constructor
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).fst = _
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).snd = _
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  obtain ⟨l, h1, h2⟩ : ∃ l : S →+* TrivSqZeroExt S S, (∀ s, (l s).fst = s) ∧ ∀ r, l (algebraMap R S r) = g r := by
    letI : Algebra R (TrivSqZeroExt S S) := g.toAlgebra
    let π : TrivSqZeroExt S S →ₐ[R] S :=
      { (TrivSqZeroExt.fstHom S S S).toRingHom with commutes' := fun r ↦ (hg r).1 }
    have hs : Function.Surjective π := fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩
    have hk : IsNilpotent (RingHom.ker (π : TrivSqZeroExt S S →+* S)) := by
      refine ⟨2, ?_⟩
      rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [RingHom.mem_ker] at hx hy
      change x.fst = 0 at hx
      change y.fst = 0 at hy
      rw [Ideal.mem_bot]
      ext
      · simp [hx]
      · simp [TrivSqZeroExt.snd_mul, hx, hy]
    let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) π hs hk
    exact ⟨l, fun s ↦ AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) π hs hk) s,
      fun r ↦ l.commutes r⟩
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s ↦ (l s).snd, map_zero' := by simp, map_add' := fun x y ↦ by rw [map_add]; rfl }) fun a b ↦ ?_,
    fun r ↦ ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h1, h1]
    simp [mul_comm]
  · change (l _).snd = _
    rw [h2, (hg r).2]

theorem derivation_extend : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  intro p _ Ω _ _ h D
  haveI : IsDomain (O0 p) := h.inj.isDomain _
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsFractionRing.lift h.inj (algebraMap (O0 p) K x)
    rw [IsFractionRing.lift_algebraMap]
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : Algebra.IsSeparable K Ω := Algebra.IsSeparable.of_integral K Ω
  haveI : Algebra.FormallyEtale K Ω := Algebra.FormallyEtale.of_isSeparable K Ω
  haveI : Algebra.FormallySmooth (O0 p) K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (O0 p))
  haveI : Algebra.FormallySmooth (O0 p) Ω := Algebra.FormallySmooth.comp (O0 p) K Ω
  exact exists_extend_of_formallySmooth D

end GlobalTheory.K5.DerExt
