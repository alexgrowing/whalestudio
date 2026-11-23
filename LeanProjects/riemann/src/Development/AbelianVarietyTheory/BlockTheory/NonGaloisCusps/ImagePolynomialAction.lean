import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

open PowerSeries GlobalTheory.BK

def shifts (U : Finset ℤ) (η : ℕ) : Finset ℤ := Finset.image₂ (· + ·) U (Finset.Icc 1 (η : ℤ))

def polyR (l e : ℕ) (U : Finset ℤ) (η : ℕ) : Polynomial ℤ :=
  ∏ n ∈ (shifts U η).erase 0, (Polynomial.X - Polynomial.C (n * e * l))

def polyR₁ (l e : ℕ) (U : Finset ℤ) (η : ℕ) : Polynomial ℤ := (polyR l e U η).divX

theorem X_mul_polyR₁ (l e : ℕ) (U : Finset ℤ) (η : ℕ) :
    Polynomial.X * polyR₁ l e U η = polyR l e U η - Polynomial.C ((polyR l e U η).eval 0) := by
  rw [polyR₁, mul_comm, ← Polynomial.coeff_zero_eq_eval_zero]
  exact eq_sub_of_add_eq (Polynomial.divX_mul_X_add _)

theorem mem_shifts {U : Finset ℤ} {η : ℕ} {n : ℤ} :
    n ∈ shifts U η ↔ ∃ i ∈ U, ∃ k : ℤ, (1 ≤ k ∧ k ≤ η) ∧ i + k = n := by
  rw [shifts, Finset.mem_image₂]
  simp only [Finset.mem_Icc]

example : shifts {-1, 0} 1 = {0, 1} := by decide

section Clauses

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

def FiniteFree : Prop := Module.Free O D.Z ∧ Module.Finite O D.Z

def Localisation : Prop :=
  Function.Injective (Descent.quotToPol D.toPhiMod η) ∧
  (∀ w : D.Pol, w ∈ D.PolEta η ↔
    ∃ n : ℕ, (l : K) ^ n • w ∈ LinearMap.range (Descent.quotToPol D.toPhiMod η)) ∧
  (D.desc.actQuot η).invariants.map (Descent.quotToPol D.toPhiMod η) = D.Z ∧
  ∀ w : D.Pol, w ∈ D.Zl ↔ ∃ n : ℕ, (l : K) ^ n • w ∈ D.Z

def Acts : Prop :=
  (∀ y ∈ divE l e η D.Man, D.EN y ∈ divE l e η D.Man) ∧
  (∀ m ∈ D.Man, D.EN m ∈ D.Man) ∧
  (∀ w ∈ D.Zl, D.Lc w ∈ D.Zl) ∧
  ∀ (g : TameGal K l e a), ∀ w ∈ D.PolEta η, D.desc.actPol g (D.Lc w) = D.Lc (D.desc.actPol g w)

def Integral : Prop := ∀ w ∈ D.Z, D.Lc w ∈ D.Z

def Semisimple (U : Finset ℤ) : Prop :=
  D.LcZ.IsSemisimple ∧
  (∀ μ : K, D.LcZ.HasEigenvalue μ → ∃ n ∈ shifts U η, μ = ((n * e * l : ℤ) : K)) ∧
  ⨆ n ∈ shifts U η, D.LcZ.eigenspace ((n * e * l : ℤ) : K) = ⊤

def Image (U : Finset ℤ) : Prop :=
  (∀ w ∈ LinearMap.range D.LcZ, Polynomial.aeval D.LcZ (polyR l e U η) w = 0 ∧
    (((polyR l e U η).eval 0 : ℤ) : K) • w =
      -D.LcZ (Polynomial.aeval D.LcZ (polyR₁ l e U η) w)) ∧
  ∀ W : Submodule K D.Zl, W ≤ W.comap D.LcZ → LinearMap.range D.LcZ ⊓ W = W.map D.LcZ

def IntegralImage (U : Finset ℤ) : Prop :=
  ∀ (c : ℤ), ∀ w ∈ LinearMap.range D.LcZ, (l : K) ^ c • (w : D.Pol) ∈ D.Z →
    ∃ z : D.Zl, (l : K) ^ c • (z : D.Pol) ∈ D.Z ∧
      (((polyR l e U η).eval 0 : ℤ) : K) • w = D.LcZ z

def Divisible : Prop :=
  (∀ w ∈ D.Z, ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z) ∧
  ∀ y ∈ D.Y, (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv

def IntegralityComputation : Prop :=
  (∀ m ∈ D.MM, ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), m = p + f) ∧
  (∀ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) ∧
  ∀ y ∈ D.EM η, ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f

end Clauses

def Valuation (l e : ℕ) (U : Finset ℤ) (η N : ℕ) : Prop :=
  (∀ n ∈ shifts U η, |n| < l) ∧
  (polyR l e U η).eval 0 ≠ 0 ∧
  padicValInt l ((polyR l e U η).eval 0) = ((shifts U η).erase 0).card ∧
  ((shifts U η).erase 0).card ≤ U.card * η ∧ U.card * η ≤ (N + 1) * η

def Statement : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (η H : ℕ) (D : BKDat O K l e a ι η H), l ≠ 2 → 1 ≤ η → η < H →
    FiniteFree D ∧ Localisation D ∧ Acts D ∧ (10 * H + 2 ≤ l → Integral D) ∧ Divisible D ∧
    ∀ (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 →
      Semisimple D U ∧ Image D U ∧ (H + η < l → Valuation l e U η N) ∧
        (10 * H + 2 ≤ l → IntegralImage D U)

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {η H : ℕ}

example {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) (hη : 1 ≤ η) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).jumps ⊆ (({j} : Finset ℤ) : Set ℤ) ∧
      j + 1 ∈ shifts {j} η ∧
      (rankOneDat O K l e a η H j h₁ h₂ 1).LcZ.HasEigenvalue (((j + 1) * e * l : ℤ) : K) := by
  refine ⟨by rw [Finset.coe_singleton]; exact (jumps_rankOne j).le, mem_shifts.2 ⟨j, by simp, 1, ⟨le_rfl, by omega⟩, rfl⟩, ?_⟩
  obtain ⟨h, h0⟩ := cls_mem_Z_rankOneDat (O := O) (K := K) (l := l) (e := e) (a := a) h₁ h₂ hη
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := ⟨_, Descent.mem_Zl_of_mem_Z _ h⟩) ⟨?_, fun h' => h0 (congrArg Subtype.val h')⟩
  rw [Module.End.mem_eigenspace_iff]
  exact Subtype.ext (Lc_rankOneDat h₁ h₂ 1)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction
