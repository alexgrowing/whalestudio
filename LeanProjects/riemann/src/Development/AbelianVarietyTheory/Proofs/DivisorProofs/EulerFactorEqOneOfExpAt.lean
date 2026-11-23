import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this

open Classical in

def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

theorem int_mul {m p r : Type} [Fintype p] {A : Matrix m p k} {B : Matrix p r k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem cball_mul {m p r : Type} [Fintype p] {s : kˣ} {A : Matrix m p k} {B : Matrix p r k}
    (hA : ∀ i j, A i j ∈ cball s) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ cball s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ (· ∈ cball s) (fun _ _ => add_mem_cball) (by simp [cball]) fun l _ => ?_
  have h1 := hA i l
  have h2 := hB l j
  simp only [cball, Set.mem_setOf_eq, map_mul] at h1 ⊢
  rw [Valuation.mem_integer_iff] at h2
  calc valuation k (A i l) * valuation k (B l j) ≤ valuation k (s : k) * 1 := mul_le_mul' h1 h2
    _ = _ := mul_one _

theorem toRows₁_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₁ = x.toRows₁ * g := by ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem toRows₂_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₂ = x.toRows₂ * g := by ext i j; simp [Matrix.toRows₂, Matrix.mul_apply]

theorem valuation_det_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : valuation k g.val.det = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val.det = algebraMap 𝒪[k] k u.val.det :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)

theorem StdSupp.mul {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x)
    {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : StdSupp ϖ c (x * g.val) := by
  have hgi := ((SplitFlip.mem_KO_iff g).1 hg).1
  refine ⟨?_, ?_, ?_⟩
  · rw [toRows₁_mul]; exact int_mul h.1 hgi
  · rw [toRows₁_mul, Matrix.det_mul, map_mul, h.2.1, valuation_det_KO hg, one_mul]
  · rw [toRows₂_mul]; exact cball_mul h.2.2 hgi

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
