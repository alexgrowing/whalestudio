import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex

noncomputable section

abbrev E4 : Type := CyclotomicField 4 ℚ

instance : NumberField E4 := inferInstanceAs (NumberField (CyclotomicField 4 ℚ))

instance : IsCyclotomicExtension {4} ℚ E4 := by
  have h : @IsCyclotomicExtension {4} ℚ E4 _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance : IsCMField E4 := IsCyclotomicExtension.Rat.isCMField E4 (S := {4}) ⟨4, rfl, by norm_num⟩

def dim0 : (E4 →+* ℂ) → ℕ := fun _ => 0

instance : IsEmpty (Idx dim0) := ⟨fun i => i.2.elim0⟩

theorem card_coordIndex_zeroDim : Fintype.card (Idx dim0) = 0 := Fintype.card_eq_zero

instance : Subsingleton (Vsp dim0) := ⟨fun x y => PiLp.ext fun i => isEmptyElim i⟩

instance : IsEmpty (Fin (2 * Fintype.card (Idx dim0))) :=
  ⟨fun i => absurd i.2 (by simp)⟩

theorem Hf0 (x y : Vsp dim0) : Hf x y = 0 := by
  simp [Hf]

def X0 : PT E4 where
  dim := dim0
  r := 0
  dim_conj := fun _ => rfl
  b := Module.Basis.empty _
  stable := fun α x _ => by rw [Subsingleton.elim (act α x) 0]; exact zero_mem _
  integral := fun _ _ _ _ => ⟨0, by simp [Hf0]⟩
  perfect := fun φ => ⟨0, zero_mem _, fun y => by
    have hy : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [hy, map_zero]; simp [Hf0]⟩
  eps := fun _ => 1
  eps_pm := fun _ _ => Or.inl rfl
  eps_add := fun _ _ _ _ => by simp [Hf0]
  eps_iso := fun _ _ _ => rfl

instance : IsEmpty (Idx X0.dim) := inferInstanceAs (IsEmpty (Idx dim0))

instance : Subsingleton (Vsp X0.dim) := inferInstanceAs (Subsingleton (Vsp dim0))

theorem mem_lattice_zeroTorus (v : Vsp X0.dim) : v ∈ X0.L := by
  rw [Subsingleton.elim v 0]; exact zero_mem _

theorem hermFormPi_zeroTorus {n : ℕ} (v w : Fin n → Vsp X0.dim) : HC v w = 0 := by
  simp only [HC]; exact Finset.sum_eq_zero fun k _ => Hf0 (v k) (w k)

theorem inhab (q n : ℕ) (_hq : 1 ≤ q) :
    IsPi X0 q LinearMap.id ∧ (fun _ : Fin 1 → Vsp X0.dim => (1 : ℂ)) ∈ X0.Sec 1 1 ∧ (fun _ : Fin 1 → Vsp X0.dim => (1 : ℂ)) ≠ 0 ∧
      IsReps X0 q n LinearMap.id {0} := by
  refine ⟨⟨fun _ _ => Subsingleton.elim _ _, fun x _ => mem_lattice_zeroTorus x, fun v w => ?_, fun x _ => ?_⟩,
    ⟨differentiable_const _, fun γ _ v => ?_⟩, fun h => one_ne_zero (congrFun h 0),
    ⟨fun b _ k => mem_lattice_zeroTorus _, fun b _ => ⟨0, ⟨Finset.mem_singleton_self _, fun k => mem_lattice_zeroTorus _⟩,
      fun y hy => Finset.mem_singleton.mp hy.1⟩⟩⟩
  · simp [Hf]
  · simp [X0]
  · rw [hermFormPi_zeroTorus, hermFormPi_zeroTorus]; simp [X0]

theorem nstatement_hyps_consistent (q n : ℕ) (hq : 1 ≤ q) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : PT E)
      (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) (s : (Fin 1 → Vsp X.dim) → ℂ)
      (K : Finset (Fin n → Vsp X.dim)),
      1 ≤ q ∧ IsPi X q π ∧ s ∈ X.Sec 1 1 ∧ s ≠ 0 ∧ IsReps X q n π K :=
  ⟨E4, inferInstance, inferInstance, inferInstance, X0, LinearMap.id, fun _ => 1, {0}, hq, inhab q n hq⟩

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
