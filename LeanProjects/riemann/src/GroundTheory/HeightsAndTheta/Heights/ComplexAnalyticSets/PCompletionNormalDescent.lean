import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompletionNormalDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion Polynomial

section

variable {R : Type} [CommRing R] (J : Ideal R)

theorem CompletionNormalDescent.evalₐ_algebraMap (n : ℕ) (x : R) :
    evalₐ J n (algebraMap R (AdicCompletion J R) x) = Ideal.Quotient.mk (J ^ n) x := by
  rw [(evalₐ J n).commutes]
  rfl

variable [IsNoetherianRing R]

theorem CompletionNormalDescent.algebraMap_injective (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    Function.Injective (algebraMap R (AdicCompletion J R)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have H : IsHausdorff J R := IsHausdorff.of_le_jacobson J R hJ
  refine H.haus a fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have := CompletionNormalDescent.evalₐ_algebraMap J n a
  rw [ha, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem CompletionNormalDescent.dvd_of_dvd_completion (hJ : J ≤ (⊥ : Ideal R).jacobson) (a b : R)
    (x : AdicCompletion J R)
    (h : algebraMap R (AdicCompletion J R) a = algebraMap R (AdicCompletion J R) b * x) : b ∣ a := by
  have H : IsHausdorff J (R ⧸ Ideal.span {b}) := IsHausdorff.of_le_jacobson J _ hJ
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  have h1 := congrArg (evalₐ J n) h
  rw [map_mul, CompletionNormalDescent.evalₐ_algebraMap, CompletionNormalDescent.evalₐ_algebraMap, ← hr,
    ← map_mul, Ideal.Quotient.eq] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {b}) a = Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) := by
    rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b), zero_mul,
      sub_zero]
  have h3 : Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) =
      (a - b * r) • (Ideal.Quotient.mk (Ideal.span {b}) 1) := by
    rw [Algebra.smul_def, _root_.map_one, mul_one]
    rfl
  rw [h2, h3]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

end

theorem CompletionNormalDescent.proof : CompletionNormalDescent.Statement := by
  intro R _ J _ hJ hD hIC
  have hinj := CompletionNormalDescent.algebraMap_injective J hJ
  have : IsDomain R := hinj.isDomain (algebraMap R (AdicCompletion J R))
  refine ⟨inferInstance, ?_⟩
  set f := algebraMap R (AdicCompletion J R) with hf
  let L := FractionRing (AdicCompletion J R)
  let g : R →+* L := (algebraMap (AdicCompletion J R) L).comp f
  have hg : Function.Injective g := (IsFractionRing.injective (AdicCompletion J R) L).comp hinj
  let φ : FractionRing R →+* L := IsFractionRing.lift hg
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap (AdicCompletion J R) L (f r) :=
    fun r => IsFractionRing.lift_algebraMap hg r
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro z hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R (FractionRing R) b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hb0

  have hint : IsIntegral (AdicCompletion J R) (φ (algebraMap R (FractionRing R) a /
      algebraMap R (FractionRing R) b)) := by
    obtain ⟨p, hp, hpz⟩ := hz
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (AdicCompletion J R) L).comp f = φ.comp (algebraMap R (FractionRing R)) := by
      ext r; exact (hφ r).symm
    rw [this, ← hom_eval₂, hpz, _root_.map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hay : f a = f b * y := by
    apply IsFractionRing.injective (AdicCompletion J R) L
    rw [map_mul, hy, map_div₀, hφ, hφ]
    have hfb : algebraMap (AdicCompletion J R) L (f b) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (AdicCompletion J R) L),
        map_eq_zero_iff _ hinj]
      exact hb0
    exact (mul_div_cancel₀ _ hfb).symm
  obtain ⟨r, rfl⟩ := CompletionNormalDescent.dvd_of_dvd_completion J hJ a b y hay
  refine ⟨r, ?_⟩
  rw [map_mul]
  exact (mul_div_cancel_left₀ _ hbK).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
