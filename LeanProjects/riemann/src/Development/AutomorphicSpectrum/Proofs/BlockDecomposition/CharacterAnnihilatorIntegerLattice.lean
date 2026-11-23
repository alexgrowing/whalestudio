import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
open ValuativeRel MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CharLattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def annihilator (ψ : AddChar k Circle) (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := fun t _ => by simp
  add_mem' := fun {x y} hx hy t ht => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := fun {x} hx t ht => by
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]

theorem isOpen_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) (hb : b ≠ 0) :
    IsOpen (annihilator ψ n b : Set (Fin n → k)) := by
  obtain ⟨γ, hγ0, hγ⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  apply AddSubgroup.isOpen_of_mem_nhds
  have hball : {z : k | valuation k z < γ} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ0
  have hmul : {y : k | valuation k (b * y) < γ} ∈ nhds (0 : k) := by
    have h := (continuous_const.mul continuous_id : Continuous fun y : k => b * y).tendsto' 0 0 (mul_zero b)
    exact h hball
  have hU : (Set.univ.pi fun _ : Fin n => {y : k | valuation k (b * y) < γ}) ∈ nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ (fun j _ => hmul)
  refine Filter.mem_of_superset hU ?_
  intro x hx t ht
  apply hγ
  show valuation k (b * ∑ i, t i * x i) < γ
  rw [Finset.mul_sum]
  refine (valuation k).map_sum_lt hγ0 fun j _ => ?_
  have hxj : valuation k (b * x j) < γ := hx j (Set.mem_univ j)
  have htj : valuation k (t j) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (ht j)
  refine lt_of_le_of_lt ?_ hxj
  calc valuation k (b * (t j * x j)) = valuation k (t j) * valuation k (b * x j) := by
        rw [← map_mul]; ring_nf
    _ ≤ 1 * valuation k (b * x j) := mul_le_mul_left htj _
    _ = valuation k (b * x j) := one_mul _

theorem isClosed_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) :
    IsClosed (annihilator ψ n b : Set (Fin n → k)) := by
  have e : (annihilator ψ n b : Set (Fin n → k)) =
      ⋂ (t : Fin n → k) (_ : ∀ j, t j ∈ 𝒪[k]), {x | ψ (b * (t ⬝ᵥ x)) = 1} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [e]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (hψ.comp (continuous_const.mul (continuous_const.dotProduct continuous_id)))
      continuous_const

theorem annihilator_subset (ψ : AddChar k Circle) (n : ℕ) (b : k) (hb : b ≠ 0) (y₀ : k)
    (hy : ψ y₀ ≠ 1) :
    (annihilator ψ n b : Set (Fin n → k)) ⊆
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (y₀ / b)}) := by
  intro x hx j _
  have hx' : ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1 := hx
  show valuation k (x j) ≤ valuation k (y₀ / b)
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  have hxj : x j ≠ 0 := by
    intro h
    rw [h, map_zero] at hlt
    exact not_lt_zero hlt
  have ht : ∀ i, (Pi.single j (y₀ / b / x j) : Fin n → k) i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, map_div₀]
      exact (div_le_one₀ ((valuation k).pos_iff.2 hxj)).2 hlt.le
    · rw [Pi.single_eq_of_ne hij, map_zero]
      exact zero_le_one
  have h := hx' _ ht
  have e : b * ((Pi.single j (y₀ / b / x j) : Fin n → k) ⬝ᵥ x) = y₀ := by
    rw [single_dotProduct]
    field_simp
  rw [e] at h
  exact hy h

theorem isCompact_isOpen_annihilator :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 →
      IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧
      IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  intro k _ _ _ _ ψ hψ hne n b hb
  have e : {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} =
      (annihilator ψ n b : Set (Fin n → k)) := rfl
  rw [e]
  obtain ⟨y₀, hy⟩ : ∃ y₀, ψ y₀ ≠ 1 := by
    by_contra h
    exact hne (AddChar.ext ψ 1 fun y => by
      rw [AddChar.one_apply]
      by_contra hy
      exact h ⟨y, hy⟩)
  refine ⟨?_, isOpen_annihilator ψ hψ n b hb⟩
  exact (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _).of_isClosed_subset
    (isClosed_annihilator ψ hψ n b) (annihilator_subset ψ n b hb y₀ hy)

end GlobalTheory.CompanionTheory.CharLattice
