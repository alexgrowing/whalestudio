import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LatticeCoset

variable {F : Type} [Field F] [ValuativeRel F] {n : ℕ}

theorem mem_unitGL_iff (h : GL (Fin n) F) :
    h ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (h : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
      (∀ i j, ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => (k.1 i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((k⁻¹).1 i j).2
  · rintro ⟨h1, h2⟩
    let O := (ValuativeRel.valuation F).integer
    let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨(h : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) O :=
      Matrix.of fun i j => ⟨((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map O.subtype = (h : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map O.subtype = ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      show (A * B).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hBA : B * A = 1 := by
      apply inj
      show (B * A).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

theorem latticeOf_subset_of_integral (g g' : GL (Fin n) F)
    (h : ∀ i j, ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    latticeOf g' ⊆ latticeOf g := by
  rintro v ⟨w, hw, rfl⟩
  refine ⟨((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hw j)
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]

theorem integral_of_latticeOf_subset (g g' : GL (Fin n) F)
    (h : latticeOf g' ⊆ latticeOf g) (i j : Fin n) :
    ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  have hs : ∀ k, (Pi.single j (1 : F) : Fin n → F) k ∈ intO F := by
    intro k
    rcases eq_or_ne k j with rfl | hk
    · rw [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hk]; exact Subring.zero_mem _
  obtain ⟨w', hw', he⟩ := h ⟨Pi.single j 1, hs, rfl⟩
  have key : ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single j 1) = w' := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hi := congrFun key i
  rw [Matrix.mulVec_single_one] at hi
  change ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = w' i at hi
  rw [hi]
  exact hw' i

theorem latticeOf_eq_iff : PositivityTheory.Rg.Tf.Loc.L1 := by
  intro F _ _ _ _ n g g'
  constructor
  · intro h
    rw [mem_unitGL_iff]
    refine ⟨integral_of_latticeOf_subset g g' h.symm.subset, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact integral_of_latticeOf_subset g' g h.subset
  · intro hm
    rw [mem_unitGL_iff] at hm
    obtain ⟨h1, h2⟩ := hm
    rw [mul_inv_rev, inv_inv] at h2
    exact Set.Subset.antisymm (latticeOf_subset_of_integral g' g h2) (latticeOf_subset_of_integral g g' h1)

end GlobalTheory.CompanionTheory.LatticeCoset
