import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_one' (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  simp

theorem minor_one' {n : ℕ} (m : Fin n) : minor (1 : GL (Fin n) k) m = 1 := by
  unfold minor
  simp [Matrix.toSquareBlockProp]

theorem continuous_minor' {n : ℕ} (m : Fin n) : Continuous fun g : GL (Fin n) k => minor g m := by
  unfold minor
  exact (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem ev_eventually_one (χ : kˣ →* ℂˣ) (S : Set k) (hS : S ∈ nhds (0 : k)) (hT : ∀ x ∈ S, Triv χ x) :
    ∀ᶠ x in nhds (1 : k), ev χ x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := triv_ev_props k
  have hball : {x : k | valuation k (x - 1) < 1} ∈ nhds (1 : k) :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_of_mem one_ne_zero
  have hpre : (fun x : k => x - 1) ⁻¹' S ∈ nhds (1 : k) :=
    (continuous_sub_right (1 : k)).continuousAt.preimage_mem_nhds (by simpa using hS)
  filter_upwards [hball, hpre] with x hx hxS
  have hv : valuation k x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hx
  rw [h8 χ x 1 hv (by simp) (hT _ hxS), ev_one']

theorem theta_one_and_near : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) →
    theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  intro k _ _ _ _ n ψ hψ
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := triv_ev_props k
  have hset : ∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → {x : k | Triv χ x} ∈ nhds (0 : k) := fun χ hχ =>
    (h6 χ hχ).1.mem_nhds (h3 χ)
  have hnxt : ∀ m, {x : k | Triv (nxt ψ m) x} ∈ nhds (0 : k) := by
    intro m
    unfold nxt
    split_ifs with h
    · exact hset _ (hψ _)
    · refine Filter.univ_mem' fun x => ?_
      intro u _ _
      rfl
  have hev : ∀ m, ∀ᶠ x in nhds (1 : k), ev (ψ m / nxt ψ m) x = 1 := fun m =>
    ev_eventually_one _ _ (Filter.inter_mem (hset _ (hψ m)) (hnxt m)) fun x hx => by
      rw [div_eq_mul_inv]
      exact h4 _ _ x hx.1 (h5 _ x hx.2)
  refine ⟨?_, ?_⟩
  · unfold theta
    exact Finset.prod_eq_one fun m _ => by rw [minor_one', ev_one']
  · have hall : ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ m, ev (ψ m / nxt ψ m) (minor g m) = 1 := by
      rw [Filter.eventually_all]
      intro m
      have hc := (continuous_minor' (k := k) m).continuousAt (x := 1)
      rw [ContinuousAt, minor_one'] at hc
      exact hc.eventually (hev m)
    exact ⟨_, hall, fun g hg => Finset.prod_eq_one fun m _ => hg m⟩

end

end GlobalTheory.PsType
