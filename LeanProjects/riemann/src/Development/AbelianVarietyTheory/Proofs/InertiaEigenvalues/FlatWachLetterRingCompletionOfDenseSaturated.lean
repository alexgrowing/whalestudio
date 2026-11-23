import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
open Formalism.BasicNotions

namespace GlobalTheory
namespace FlatCompl

section Level

variable {A R E : Type} [CommRing A] [CommRing R] [CommRing E] [Algebra A R] [Algebra A E]
  [Algebra R E] [IsScalarTower A R E]

theorem mem_pow_smul_top_iff (p : ℕ) (n : ℕ) (e : E) :
    e ∈ ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R E) ↔ e ∈ Ideal.span {(p : E) ^ n} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by simp [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, Submodule.mem_top, by simp [Algebra.smul_def, mul_comm]⟩

variable (s : A) [IsLocalization.Away s R] (p : ℕ)

theorem level_surj
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (n : ℕ) (e : E) : ∃ r : R, algebraMap R E r - e ∈ Ideal.span {(p : E) ^ n} := by
  obtain ⟨a, m, h⟩ := hd e n
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  refine ⟨algebraMap A R a * ↑u⁻¹, ?_⟩
  have hE : algebraMap R E ↑u * algebraMap R E ↑u⁻¹ = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have key : algebraMap R E (algebraMap A R a * ↑u⁻¹) - e =
      -((e * algebraMap A E (s ^ m) - algebraMap A E a) * algebraMap R E ↑u⁻¹) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A R E (s ^ m),
      map_pow, ← hu]
    linear_combination e * hE
  rw [key]
  exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _ h)

include s in
theorem level_inj
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b)
    (n : ℕ) (r : R) (h : algebraMap R E r ∈ Ideal.span {(p : E) ^ n}) :
    r ∈ Ideal.span {(p : R) ^ n} := by
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers s) r
  simp only at hr
  have hE : algebraMap A E a ∈ Ideal.span {(p : E) ^ n} := by
    rw [IsScalarTower.algebraMap_apply A R E, ← hr, map_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨b, rfl⟩ := hsat a n hE
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap A R b * ↑u⁻¹, ?_⟩
  have h1 : r = r * (↑u * ↑u⁻¹) := by simp
  rw [h1, ← mul_assoc, hu, ← map_pow, hr]
  simp only [map_mul, map_pow, map_natCast]
  ring

end Level

end FlatCompl
end GlobalTheory

namespace GlobalTheory
namespace FlatCompl

open AdicCompletion

theorem flat_of_dense_sat {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [Algebra A E]
    (s : A) (p : ℕ) (hs : IsUnit (algebraMap A E s))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b) :
    Module.Flat A E := by
  let R := Localization.Away s
  letI : Algebra R E := (IsLocalization.Away.lift s hs).toAlgebra
  haveI : IsScalarTower A R E :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq _ a).symm)
  let I : Ideal R := Ideal.span {(p : R)}
  have hmap : I.map (algebraMap R E) = Ideal.span {(p : E)} := by
    simp [I, Ideal.map_span]
  haveI : IsAdicComplete I E := by
    have h1 : IsHausdorff I E :=
      IsHausdorff.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsHausdorff)
    have h2 : IsPrecomplete I E :=
      IsPrecomplete.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsPrecomplete)
    exact { toIsHausdorff := h1, toIsPrecomplete := h2 }
  let f : R →ₗ[R] E := Algebra.linearMap R E
  have hinj : ∀ n, Function.Injective (f.reduceModIdeal (I ^ n)) := by
    intro n
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H r =>
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff (E := R)]
      exact level_inj s p hsat n r ((mem_pow_smul_top_iff p n _).mp hx)
  have hsurj : ∀ n, Function.Surjective (f.reduceModIdeal (I ^ n)) := by
    intro n y
    induction y using Submodule.Quotient.induction_on with
    | H e =>
      obtain ⟨r, hr⟩ := level_surj (R := R) s p hd n e
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq, mem_pow_smul_top_iff]
      exact hr
  have hbij : Function.Bijective (AdicCompletion.map I f) := by
    constructor
    · intro x y hxy
      ext n
      apply hinj n
      have := congrArg (fun z => z.val n) hxy
      simpa only [AdicCompletion.map_val_apply] using this
    · intro y
      let g := fun n => Function.surjInv (hsurj n)
      refine ⟨⟨fun n => g n (y.val n), fun {m n} hmn => ?_⟩, ?_⟩
      · apply hinj m
        have h1 := LinearMap.congr_fun
          (AdicCompletion.transitionMap_comp_reduceModIdeal I f hmn) (g n (y.val n))
        simp only [LinearMap.coe_comp, Function.comp_apply] at h1
        rw [show (f.reduceModIdeal (I ^ m)) (transitionMap I R hmn (g n (y.val n))) =
          transitionMap I E hmn (f.reduceModIdeal (I ^ n) (g n (y.val n))) from h1.symm]
        rw [Function.surjInv_eq (hsurj n), Function.surjInv_eq (hsurj m)]
        exact y.property hmn
      · ext n
        exact Function.surjInv_eq (hsurj n) _
  let Φ : AdicCompletion I R ≃ₗ[R] E :=
    (LinearEquiv.ofBijective ((AdicCompletion.map I f).restrictScalars R) hbij).trans
      (AdicCompletion.ofLinearEquiv I E).symm
  haveI : Module.Flat R E := Module.Flat.of_linearEquiv Φ.symm
  haveI : Module.Flat A R := IsLocalization.flat R (Submonoid.powers s)
  exact Module.Flat.trans A R E

end FlatCompl
end GlobalTheory

namespace GlobalTheory

theorem flat_letA_of_dense_sat : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (p : ℕ) (E : Type) [CommRing E] [Algebra (LetA O n) E], IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E :=
  fun _ _ _ _ _ p _ _ _ hs hc hd hsat => FlatCompl.flat_of_dense_sat letπ p hs hc hd hsat

end GlobalTheory
