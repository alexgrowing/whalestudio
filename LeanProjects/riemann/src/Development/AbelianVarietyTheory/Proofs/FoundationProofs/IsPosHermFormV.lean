import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Complex
open scoped BigOperators ComplexConjugate Real

noncomputable section

namespace GlobalTheory.UnitaryTheta

section General

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsPosHerm (H : Sesq V) : Prop :=
  (∀ z w, H z w = conj (H w z)) ∧ ∀ z, z ≠ 0 → 0 < (H z z).re

def Heisenberg₂ (H : Sesq V) (x : V) (G : V → ℂ) : V → ℂ :=
  fun z => G (z + x) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2)

def kerTerm (H : Sesq V) (x w z : V) : ℂ :=
  cexp ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2)

def kerSum (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (z : V) : V → ℂ :=
  fun w => ∑' x : Λ, α x * kerTerm H x w z

def IsSemichar (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) : Prop :=
  (∀ x ∈ Λ, α x = 1 ∨ α x = -1) ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, (H x y).im = m) ∧
    ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * cexp (-((π : ℂ) * I) * ((H x y).im : ℂ))

end General

def formV (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (fun z z' w => by simp [Hf, add_mul, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_assoc, mul_div_assoc'])
    (fun z w w' => by simp [Hf, mul_add, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_left_comm, mul_div_assoc'])

@[simp] theorem formV_apply (D : D7) (T : Tor D) {N N' : ℕ} (z w : VC D N N') :
    formV D T N N' z w = Hf D T z w := rfl

theorem heis_formV (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) :
    Heisenberg₂ (formV D T N N') x G = U D T x G := rfl

open NumberField Classical in
open Complex in
open scoped BigOperators ComplexConjugate Real in
theorem _root_.GlobalTheory.UnitaryTheta.isPosHerm_formV (D : _root_.Formalism.BasicNotions.D7) (T : _root_.Formalism.MainNotions.TaylorLogMetric.Tor D)
    (N N' : ℕ) (h : 0 < _root_.Formalism.MainNotions.TaylorLogMetric.area T.abelian₂) :
    _root_.GlobalTheory.UnitaryTheta.IsPosHerm (_root_.GlobalTheory.UnitaryTheta.formV D T N N') := by
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  · simp only [_root_.GlobalTheory.UnitaryTheta.formV_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, map_div₀, map_sum, map_mul,
      Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have hsum : ∀ τ i j, z τ i j * conj (z τ i j) = ((Complex.normSq (z τ i j) : ℝ) : ℂ) :=
      fun τ i j => Complex.mul_conj _
    simp only [_root_.GlobalTheory.UnitaryTheta.formV_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, hsum]
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
    refine div_pos ?_ h
    obtain ⟨τ, i, j, hz⟩ : ∃ τ i j, z τ i j ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz (funext fun τ => funext fun i => funext fun j => hne τ i j)
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨τ, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 hz⟩

end GlobalTheory.UnitaryTheta
