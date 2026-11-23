import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

namespace GlobalTheory.InvAlg

theorem factorPow_evalₐ {A : Type} [CommRing A] (I : Ideal A) {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule A A) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} {J : Ideal B}
    (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n)

def adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (pow_le_comap f h n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)

theorem factorPow_comp_adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (adicCompletionMapToQuotientPow f I J h n) = adicCompletionMapToQuotientPow f I J h k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionMapToQuotientPow, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (adicCompletionMapToQuotientPow f I J h) (factorPow_comp_adicCompletionMapToQuotientPow f I J h)

theorem evalₐ_cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (cmap f I J h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap f h n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (factorPow_comp_adicCompletionMapToQuotientPow f I J h) n x

theorem cmap_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (a : A) : cmap f I J h (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_cmap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem map_algebraMap_le {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (g : B →ₐ[A] B') (J : Ideal A) : (J.map (algebraMap A B)).map (g : B →+* B') ≤ J.map (algebraMap A B') := by
  rw [Ideal.map_map, g.comp_algebraMap]

def galAlg {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) :
    R' →ₐ[R] R' :=
  { σ.1.toRingHom with commutes' := σ.2 }

@[simp] theorem galAlg_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : R') : galAlg σ x = σ.1 x := rfl

def galTensor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O] [Algebra R O]
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : TensorProduct R O R' →ₐ[O] TensorProduct R O R' :=
  Algebra.TensorProduct.map (AlgHom.id O O) (galAlg σ)

@[simp] theorem galTensor_tmul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O]
    [Algebra R O] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : O) (y : R') :
    galTensor O σ (x ⊗ₜ[R] y) = x ⊗ₜ[R] σ.1 y := rfl

end GlobalTheory.InvAlg
