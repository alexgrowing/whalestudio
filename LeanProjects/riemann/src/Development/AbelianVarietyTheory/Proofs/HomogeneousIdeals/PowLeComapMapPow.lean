import Mathlib

universe u_1 u_2

namespace GlobalTheory.PowerExtensionEvaluation

theorem pow_le_comap_map_pow {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (Ideal.map_pow f I n))

theorem factorPow_evalₐ {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s.val n) = Ideal.Quotient.mk (I ^ m) (s.val m)
  rw [Ideal.Quotient.eq]
  have h := s.property hle
  rw [SModEq.sub_mem] at h
  have h2 : s.val m - s.val n ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  have h3 := (I ^ m).neg_mem h2
  rwa [neg_sub] at h3

theorem exists_extension {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by
  let F : (n : ℕ) → AdicCompletion I A →+* B ⧸ (Ideal.map f I) ^ n := fun n =>
    (Ideal.quotientMap ((Ideal.map f I) ^ n) f (pow_le_comap_map_pow I f n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.map f I) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hm : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) a := by
      rw [← factorPow_evalₐ I hle x, ← ha]
      rfl
    change Ideal.Quotient.factorPow (Ideal.map f I) hle
        (Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap _ f (pow_le_comap_map_pow I f m) (AdicCompletion.evalₐ I m x)
    rw [← ha, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (Ideal.map f I) F hF, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.map f I)
  intro n a
  rw [RingHom.coe_comp, Function.comp_apply, IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A a)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

end GlobalTheory.PowerExtensionEvaluation
