import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def normForm (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {n : ℕ}
    (η : Fin n → S) : MvPolynomial (Fin n) R := by
  classical
  exact (Matrix.of fun i j =>
    ∑ m, X m * C (Algebra.leftMulMatrix (Module.Free.chooseBasis R S) (η m) i j)).det

def NormFormEval.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] (n : ℕ)
    (η : Fin n → S) (u : Fin n → R),
    eval u (normForm R S η) = Algebra.norm R (∑ m, u m • η m)

def NormFormEmbeddings.Statement : Prop :=
  ∀ (K L Ω : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (η : Fin n → L),
    map (algebraMap K Ω) (normForm K L η) = ∏ σ : L →ₐ[K] Ω, ∑ m, X m * C (σ (η m))

def LinearFormPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (a : Fin n → F), a ≠ 0 →
    Prime (∑ m, X m * C (a m) : MvPolynomial (Fin n) F)

def MapDvdDescent.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : Type) (f g : MvPolynomial σ K),
    map (algebraMap K Ω) f ∣ map (algebraMap K Ω) g → f ∣ g

def NormFormDvd.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (n : ℕ) (η : Fin n → L) (t : Fin n → K) (P : MvPolynomial (Fin n) K),
    Algebra.adjoin K (Set.range η) = ⊤ → ∑ m, t m • η m = 1 →
      (∑ m, X m * C (η m)) ∣ map (algebraMap K L) P → normForm K L η ∣ P

def PrimeMapFractionRing.Statement : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ)
    (P : MvPolynomial (Fin n) O),
    Prime P → (∀ a : O, P ≠ C a) → Prime (map (algebraMap O K) P)

section Inhabitants

theorem LinearFormPrime.hypotheses_inhabited : (fun _ : Fin 1 => (1 : ℚ)) ≠ 0 :=
  fun h => one_ne_zero (congrFun h 0)

theorem NormFormEmbeddings.hypotheses_inhabited :
    Infinite ℚ ∧ FiniteDimensional ℚ ℚ ∧ Algebra.IsSeparable ℚ ℚ ∧ IsAlgClosed (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem NormFormDvd.hypotheses_inhabited :
    Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ))) = ⊤ ∧
      ∑ m : Fin 1, (fun _ : Fin 1 => (1 : ℚ)) m • (fun _ : Fin 1 => (1 : ℚ)) m = 1 ∧
      (∑ m : Fin 1, X m * C ((fun _ : Fin 1 => (1 : ℚ)) m)) ∣
        map (algebraMap ℚ ℚ) (X 0 : MvPolynomial (Fin 1) ℚ) := by
  refine ⟨?_, by simp, by simp⟩
  rw [eq_top_iff]
  intro x _
  exact Subalgebra.algebraMap_mem (Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ)))) x

theorem PrimeMapFractionRing.hypotheses_inhabited :
    Prime (X 0 : MvPolynomial (Fin 1) ℤ) ∧ ∀ a : ℤ, (X 0 : MvPolynomial (Fin 1) ℤ) ≠ C a :=
  ⟨X_prime, fun a h => by
    have h' := congrArg totalDegree h
    rw [totalDegree_X, totalDegree_C] at h'
    exact one_ne_zero h'⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights
