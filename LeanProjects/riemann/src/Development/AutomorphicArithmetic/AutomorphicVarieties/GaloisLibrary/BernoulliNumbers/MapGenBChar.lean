import Mathlib

noncomputable section

open Finset

namespace UpperTheory.V.Bern

def bcoef (N k a : ℕ) : ℚ := (N : ℚ) ^ ((k : ℤ) - 1) * (Polynomial.bernoulli k).eval ((a : ℚ) / N)

def genB {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) : R :=
  ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * algebraMap ℚ R (bcoef N k a)

def primVal {R : Type*} [CommRing R] {N : ℕ} (χ : DirichletCharacter R N) (a : ℕ) : R :=
  χ.primitiveCharacter (a : ZMod χ.conductor)

def Bprim {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N) : R :=
  genB k (χ.primitiveCharacter : ZMod χ.conductor → R)

def Lprim {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  χ.primitiveCharacter.LFunction s

def charSet (Ω : Type*) [CommRing Ω] {N : ℕ} (P : Set (Subgroup (ZMod N)ˣ)) : Set (DirichletCharacter Ω N) :=
  {χ | χ.toUnitHom.ker ∈ P}

def parKer (N k : ℕ) : Set (Subgroup (ZMod N)ˣ) := {K | (-1 : (ZMod N)ˣ) ∈ K ↔ Even k}

def den (N k : ℕ) : ℕ := N * primorial (k + 1)

def bnd (N k : ℕ) : ℝ := 16 * (N : ℝ) ^ (k + 1) * (k.factorial : ℝ)

theorem map_genB {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} (f : R →+* S) (k : ℕ)
    (Φ : ZMod N → R) : f (genB k Φ) = genB k (fun a => f (Φ a)) := by
  unfold genB
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, RingHom.map_rat_algebraMap]

theorem map_genB_char {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} (f : R →+* S) (k : ℕ)
    (χ : DirichletCharacter R N) : f (genB k χ) = genB k (χ.ringHomComp f : ZMod N → S) := by
  rw [map_genB]
  congr 1

theorem genB_mem {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) (A : Subalgebra ℚ R)
    (h : ∀ a, Φ a ∈ A) : genB k Φ ∈ A := by
  unfold genB
  exact A.sum_mem fun a _ => A.mul_mem (h _) (A.algebraMap_mem _)

theorem Bprim_eq {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N) :
    Bprim k χ = ∑ a ∈ Icc 1 χ.conductor, primVal χ a * algebraMap ℚ R (bcoef χ.conductor k a) := rfl

theorem den_pos {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 < den N k := by
  unfold den
  exact Nat.mul_pos hN (primorial_pos _)

theorem den_dvd {M N : ℕ} (h : M ∣ N) (k : ℕ) : den M k ∣ den N k := by
  unfold den
  exact Nat.mul_dvd_mul_right h _

example : bcoef 1 1 1 = 1 / 2 := by norm_num [bcoef]
example : bcoef 3 1 1 - bcoef 3 1 2 = -1 / 3 := by norm_num [bcoef]

end UpperTheory.V.Bern

end
