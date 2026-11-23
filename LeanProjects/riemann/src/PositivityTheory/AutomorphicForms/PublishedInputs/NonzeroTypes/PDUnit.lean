import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace P_DUnit

theorem isUnit_det_sub (A : GL (Fin n) 𝒪[k]) (a : Fin G.s)
    (hA : ∀ i j, G.bl j < G.bl i → (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
      (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  set M := (IsLocalRing.residue 𝒪[k]).mapMatrix (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hdet : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact (Matrix.isUnits_det_units A).map _
  have htri := Matrix.twoBlockTriangular_det M (fun i => G.bl i ≤ a) (fun i hi j hj => by
    rw [hM, RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff]
    exact hA i j (lt_of_le_of_lt hj (not_le.1 hi)))
  rw [htri] at hdet
  have h1 := isUnit_of_mul_isUnit_left hdet
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  exact h1.ne_zero

end P_DUnit

theorem step_DUnit : ModulusOnUnitsProp G := by
  intro hb g hg a
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hg.1
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hA : ∀ i j, G.bl j < G.bl i →
      (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j hij
    obtain ⟨y, hy, hyx⟩ := hg.2 i j hij
    have hc : cc G.μ (G.bl j) (G.bl i) ≠ 0 := by
      have := hb.1 (G.bl j) (G.bl i) (ne_of_lt hij)
      omega
    have : y = (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j := hinj (by rw [hyx]; rfl)
    rw [← this]
    exact Ideal.pow_le_self hc hy
  have hu := P_DUnit.isUnit_det_sub G A a hA
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  rfl

end UpperTheory.TNZ.Grp
