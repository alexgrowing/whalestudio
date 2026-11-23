import Mathlib

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section TopNil

variable {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M]

def topNil (I : Ideal R) (T : κ → Module.End R M) : Submodule R M where
  carrier := {m | ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M)}
  add_mem' ha hb i j := ((ha i j).and (hb i j)).mono fun _ h => by
    rw [map_add]; exact add_mem h.1 h.2
  zero_mem' _ _ := Eventually.of_forall fun _ => by rw [map_zero]; exact zero_mem _
  smul_mem' c _ h i j := (h i j).mono fun _ h => by
    rw [map_smul]; exact Submodule.smul_mem _ c h

theorem mem_topNil {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := Iff.rfl

theorem mem_topNil_iff_exists {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∃ r : ℕ, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := by
  rw [mem_topNil]
  refine forall₂_congr fun i j => ⟨fun h => h.exists, fun ⟨r, hr⟩ => ?_⟩
  filter_upwards [eventually_ge_atTop r] with s hs
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [add_comm r t, pow_add, Module.End.mul_apply]
  have hle : (I ^ j • ⊤ : Submodule R M).map (T i ^ t) ≤ I ^ j • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨_, hr, rfl⟩

end TopNil

section Split

open Polynomial

variable {R : Type} [CommRing R] (P : R[X]) (n : ℕ)

def splitIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun k : ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).coeff k)

abbrev SplitAlg : Type := MvPolynomial (Fin n) R ⧸ splitIdeal P n

def SplitAlg.root (i : Fin n) : SplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem SplitAlg.prod_root :
    ∏ i : Fin n, (X - C (SplitAlg.root P n i)) = P.map (algebraMap R (SplitAlg P n)) := by
  have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) -
      P.map MvPolynomial.C).map (Ideal.Quotient.mk (splitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨k, rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  exact h2

def SplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) : SplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).map
        (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C =
          algebraMap R A := RingHom.ext fun r => by simp
      rw [h3, ← h]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem SplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) (i : Fin n) :
    SplitAlg.lift P n a h (SplitAlg.root P n i) = a i := by
  show MvPolynomial.aeval a (MvPolynomial.X i) = a i
  exact MvPolynomial.aeval_X a i

theorem SplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : SplitAlg P n →ₐ[R] A}
    (h : ∀ i, f (SplitAlg.root P n i) = g (SplitAlg.root P n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end Split

end UpperTheory.V.AlgebraTools
