import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockModelB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}

def genericT (K : Type) [Field K] (r : ℕ) : Fin r → LatticeField K r :=
  fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)

theorem algebraicIndependent_genericT : AlgebraicIndependent ℚ (genericT K r) := by
  have h := (MvPolynomial.algebraicIndependent_X (Fin r) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin r) K) (LatticeField K r)) (IsFractionRing.injective _ _)
  exact h.restrictScalars (algebraMap ℚ K).injective

theorem genericT_eq (j : Fin r) : genericT K r j = dehom K r (latticeForm (Pi.single j.succ 1)) := by
  simp [genericT, dehom, latticeForm, Pi.single_apply, genericVal]

theorem latticeCoord_ne_zero (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : latticeCoord φ ⟨(), b⟩ ≠ 0 := by
  rw [latticeCoord_eq]
  exact dehom_latticeForm_ne_zero (hφ.independent.ne_zero b)

theorem dehom_latticeForm_sum (c : Fin (N + 1) → ℤ) :
    dehom K r (latticeForm (∑ b, c b • φ b)) = ∑ b, (c b : LatticeField K r) * latticeCoord φ ⟨(), b⟩ := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul, latticeCoord_eq]
  simp [dehom]

theorem dehom_div_mem_adjoin (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈
      IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  set E := IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1)))
  have hb : ∀ b, latticeCoord φ ⟨(), b⟩ / latticeCoord φ ⟨(), 0⟩ ∈ E := fun b ↦
    IntermediateField.subset_adjoin _ _ ⟨⟨(), b⟩, rfl⟩
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ _).mp hnu
  have h1 : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈ E := by
    rw [← dehom_latticeForm_intSmul, ← hc, dehom_latticeForm_sum, Finset.sum_div]
    refine sum_mem fun b _ ↦ ?_
    rw [mul_div_assoc]
    exact mul_mem (intCast_mem _ _) (hb b)
  have h2 : (n : LatticeField K r) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h3 := div_mem h1 (intCast_mem E n)
  have e : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ / n =
      dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ := by
    field_simp
  rwa [e] at h3

theorem genericT_mem_adjoin (hL : L.FG) (hφ : IsDualBasis L φ) (j : Fin r) :
    genericT K r j ∈ IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  have h := div_mem (dehom_div_mem_adjoin hL hφ (Pi.single j.succ 1))
    (dehom_div_mem_adjoin hL hφ (Pi.single 0 1))
  have hy := latticeCoord_ne_zero hφ 0
  rw [dehom_single_zero, ← genericT_eq] at h
  have e : genericT K r j / latticeCoord φ ⟨(), 0⟩ / (1 / latticeCoord φ ⟨(), 0⟩) = genericT K r j := by
    field_simp
  rwa [e] at h

theorem isAlgebraic_dehom (u : Fin (r + 1) → K) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) (dehom K r (latticeForm u)) := by
  set E := IntermediateField.adjoin ℚ (Set.range (genericT K r))
  rw [← Subalgebra.mem_algebraicClosure, dehom_latticeForm_apply]
  refine sum_mem fun j _ ↦ mul_mem ?_ ?_
  · rw [Subalgebra.mem_algebraicClosure]
    have h : IsAlgebraic ℚ (algebraMap K (LatticeField K r) (u j)) := by
      simpa using (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (u j)).algHom
        (IsScalarTower.toAlgHom ℚ K (LatticeField K r))
    exact h.tower_top E
  · rw [Subalgebra.mem_algebraicClosure]
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [genericVal] using isAlgebraic_one (R := E) (A := LatticeField K r)
    · have hi : genericT K r i ∈ E := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa [genericVal, genericT] using isAlgebraic_algebraMap (R := E) (A := LatticeField K r) ⟨_, hi⟩

theorem ratios_isAlgebraic (s : LatticeField K r)
    (hs : s ∈ coneRatios (latticeCoord φ) (fun _ : Unit ↦ (0 : Fin (N + 1)))) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) s := by
  obtain ⟨p, rfl⟩ := hs
  have h0 := isAlgebraic_dehom (r := r) (φ 0)
  have hp := isAlgebraic_dehom (r := r) (φ p.2)
  have e : latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩ =
      dehom K r (latticeForm (φ p.2)) * (dehom K r (latticeForm (φ 0)))⁻¹ := by
    rw [latticeCoord_eq, latticeCoord_eq, div_eq_mul_inv]
  change IsAlgebraic _ (latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩)
  rw [e]
  exact hp.mul h0.inv

end LatticeModel

theorem OneBlockModel.proof (hCC : CoordConeArithVar.Statement) : OneBlockModel.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨⟨LatticeModel.latticeVariety φ hφ, rfl⟩, LatticeModel.mCoordIdeal_latticeCoord φ, ?_,
    LatticeModel.birational_latticeCoord F.fg hφ, fun m hm ↦ LatticeModel.latticeMap_image_homogeneous hφ hm⟩
  rw [← LatticeModel.mCoordIdeal_latticeCoord φ]
  exact hCC Unit (blockIdx fun _ : Unit ↦ N) (LatticeField K r) (latticeCoord φ) (fun _ ↦ 0) r
    (LatticeModel.genericT K r) ⟨()⟩ (fun _ ↦ LatticeModel.latticeCoord_ne_zero hφ 0)
    LatticeModel.algebraicIndependent_genericT (LatticeModel.genericT_mem_adjoin F.fg hφ)
    LatticeModel.ratios_isAlgebraic

end

end GroundTheory.Heights₂.Heights
