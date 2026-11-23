import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

namespace GlobalTheory.EtC.GmStep

variable (R : Type) [CommRing R]

def rowD (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) :
    H R (disc.obj (E.obj (op ⦋p⦌))) F s →+ H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s

def RowExact (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) : Prop :=
  ∀ y : H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s, rowD R E F s (p + 1) y = 0 → ∃ z, rowD R E F s p z = y

variable {R}

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
private theorem map_rowDifferential_of_commute_faces_lemma {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s) :
    φ (p + 1) (_root_.GlobalTheory.EtC.GmStep.rowD R E F s p y) =
      _root_.GlobalTheory.EtC.GmStep.rowD R E' F' s' p (φ p y) := by
  simp only [_root_.GlobalTheory.EtC.GmStep.rowD, AddMonoidHom.finset_sum_apply,
    AddMonoidHom.smul_apply, map_sum, map_zsmul, hc]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.rowExact_transfer {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hφ : ∀ p, Function.Bijective (φ p))
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (h : _root_.GlobalTheory.EtC.GmStep.RowExact R E F s p) : _root_.GlobalTheory.EtC.GmStep.RowExact R E' F' s' p := by
  intro y' hy'
  obtain ⟨y, rfl⟩ := (hφ (p + 1)).2 y'
  have hy : _root_.GlobalTheory.EtC.GmStep.rowD R E F s (p + 1) y = 0 := by
    apply (hφ (p + 1 + 1)).1
    rw [map_rowDifferential_of_commute_faces_lemma φ hc, hy', map_zero]
  obtain ⟨z, rfl⟩ := h y hy
  exact ⟨φ p z, (map_rowDifferential_of_commute_faces_lemma φ hc p z).symm⟩

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f) (laurentVarUnit B)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  simp [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_C]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℤ) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  have hu : ((_root_.GlobalTheory.EtC.laurentVarUnit B : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  have hinv : (((_root_.GlobalTheory.EtC.laurentVarUnit B)⁻¹ : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T (-1) := by
    rw [← Units.inv_mul_cancel_left (_root_.GlobalTheory.EtC.laurentVarUnit B)
      (LaurentPolynomial.T (-1)), hu, ← LaurentPolynomial.T_add]
    simp
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_T]
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, hu, ← LaurentPolynomial.T_add]
  · rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C =
      (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f :=
  RingHom.ext fun a => _root_.GlobalTheory.EtC.GmStep.laurentMap_C f a

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f p).coeff = Finsupp.mapRange f f.map_zero p.coeff := by
  refine LaurentPolynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq,
      Finsupp.mapRange_add (map_add f)]
  · rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.mapRange_single]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_isIntegral {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) : (_root_.GlobalTheory.EtC.GmStep.laurentMap f).IsIntegral := by
  letI := (_root_.GlobalTheory.EtC.GmStep.laurentMap f).toAlgebra
  intro x
  change IsIntegral (LaurentPolynomial A) x
  refine LaurentPolynomial.induction_on' x (fun p q hp hq => hp.add hq) (fun n b => ?_)
  refine IsIntegral.mul ?_ ?_
  · obtain ⟨P, hm, hP⟩ := hf b
    refine ⟨P.map LaurentPolynomial.C, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C)
      (LaurentPolynomial.C b) P = 0
    rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C, ← Polynomial.hom_eval₂, hP, map_zero]
  · rw [← _root_.GlobalTheory.EtC.GmStep.laurentMap_T f n]
    exact isIntegral_algebraMap

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_ker {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    RingHom.ker (_root_.GlobalTheory.EtC.GmStep.laurentMap f) ≤ nilradical (LaurentPolynomial A) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hc : ∀ n, f (x.coeff n) = 0 := by
    intro n
    have h := congrArg (fun g => g n) (_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff f x)
    rw [hx] at h
    simpa using h.symm
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T]
  refine Ideal.mul_mem_right _ _ ?_
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk (RingHom.mem_ker.mpr (hc n)))).map _)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.EtC.GmStep.spec_integral_surj {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hi : φ.IsIntegral) (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ⟨?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  intro P
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B)
    (fun a ha => nilradical_le_prime P.asIdeal
      (hk (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)))))
  refine ⟨⟨Q, hQ⟩, ?_⟩
  change PrimeSpectrum.comap φ ⟨Q, hQ⟩ = P
  exact PrimeSpectrum.ext hQP

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev baseHom : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev laurentHom : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constSq : Arrow.mk (yoneda.map (laurentHom A A')) ⟶ Arrow.mk (yoneda.map (baseHom A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentMap_comp_C])

def cechC : cech (laurentHom A A') ⟶ cech (baseHom A A') := Arrow.mapCechNerve (constSq A A')

def augK (k : ℕ) : disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌)) ⟶ sch.obj (Spec (CommRingCat.of (LaurentPolynomial A))) :=
  disc.map ((cechAug (laurentHom A A')).app (op ⦋k⦌))

def rowOne (q : ℕ) (i : ℤ) (k : ℕ) :
    Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) 0 (i - 1) →+ Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) 1 i where
  toFun a := (cup q (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a)
    (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A)))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add, AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC.GmStep

end
