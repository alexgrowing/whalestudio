import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.PtsMem

theorem inc_injective (D : D7) : Function.Injective (inc D) := by
  haveI : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField ℚ)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion ℚ) = 1 := congrArg (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ => x v) h
    exact zero_ne_one h2
  haveI : Nontrivial (AE D) := by
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight :
        IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AE D) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ D.host.E).injective
    exact hinj.nontrivial
  exact (inc D).injective

theorem sgA_inc (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem mem_GA (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) :
    g ∈ GA D N ↔ ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
      (g : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  have h1 : (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  change ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : Matrix (Fin N) (Fin N) (AE D)) =
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) ↔ _
  rw [h1, Matrix.mul_one]

theorem map_ct (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) :
    ((γ.map D.host.conj).transpose).map (inc D) = ((γ.map (inc D)).map (sgA D)).transpose := by
  ext i j
  simp [sgA_inc]

theorem unitary_of_isRat (D : D7) {N : ℕ} (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : γ * (γ.map D.host.conj).transpose = 1 := by
  have hg := (mem_GA D _).1 g.2
  unfold IsRat at h
  rw [h, ← map_ct, ← Matrix.map_mul] at hg
  rw [mul_eq_one_comm]
  apply Matrix.map_injective (inc_injective D)
  simp only
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_isRat (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : γ * (γ.map D.host.conj).transpose = 1) :
    ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ := by
  have h' : (γ.map D.host.conj).transpose * γ = 1 := mul_eq_one_comm.1 h
  have a : γ.map (inc D) * ((γ.map D.host.conj).transpose).map (inc D) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : ((γ.map D.host.conj).transpose).map (inc D) * γ.map (inc D) = 1 := by
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨⟨_, _, a, b⟩, (mem_GA D _).2 ?_⟩, rfl⟩
  change ((γ.map (inc D)).map (sgA D)).transpose * γ.map (inc D) = 1
  rw [← map_ct, b]

def ratSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {g | ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ}
  one_mem' := ⟨1, by
    unfold IsRat
    rw [Matrix.map_one _ (map_zero _) (map_one _)]; rfl⟩
  mul_mem' := by
    rintro a b ⟨γ, ha⟩ ⟨γ', hb⟩
    refine ⟨γ * γ', ?_⟩
    unfold IsRat at *
    rw [Matrix.map_mul, ← ha, ← hb]; rfl
  inv_mem' := by
    rintro a ⟨γ, ha⟩
    refine ⟨(γ.map D.host.conj).transpose, ?_⟩
    have hg := (mem_GA D _).1 a.2
    unfold IsRat at *
    rw [map_ct, ← ha]
    exact Units.inv_eq_of_mul_eq_one_left hg

def intSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {k | IntG D (k : GL (Fin N) (AE D))}
  one_mem' := by
    intro i j
    have : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact ⟨this, by simpa using this⟩
  mul_mem' := by
    intro a b ha hb i j
    constructor
    · rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (ha i l).1 (hb l j).1
    · rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hb i l).2 (ha l j).2
  inv_mem' := by
    intro a ha i j
    refine ⟨(ha i j).2, ?_⟩
    rw [Subgroup.coe_inv, inv_inv]
    exact (ha i j).1

end GlobalTheory.NormSum.PtsMem

open GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.NormSum.mem_ratG_intG : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  intro D N
  refine ⟨fun g => ?_, fun k => ?_, exists_isRat D, unitary_of_isRat D, inc_injective D⟩
  · have : ratG D N = ratSub D N := Subgroup.closure_eq (ratSub D N)
    rw [this]; rfl
  · have : intG D N = intSub D N := Subgroup.closure_eq (intSub D N)
    rw [this]; rfl
