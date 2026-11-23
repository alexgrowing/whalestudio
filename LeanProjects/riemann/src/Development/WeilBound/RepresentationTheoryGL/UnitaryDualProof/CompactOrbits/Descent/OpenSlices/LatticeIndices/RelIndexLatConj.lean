import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.OneAddMemZeroLattice
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.DtExistsScaleFin

noncomputable section

open Matrix GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLT

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT.Bi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem Bi.Lat_eq_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    Lat Z m = (Lat Z 0).map (smulA (pi k ^ m)) := by
  simpa using Lat_add Z m 0

private theorem smulA_injective' (m : ℕ) :
    Function.Injective (smulA (k := k) (n := n) (pi k ^ m)) := by
  have hp : pi k ^ m ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff _).1 (GLnLocal.valuation_uniformizer_ne_zero k))
  intro x y hxy
  exact smul_right_injective (Matrix (Fin n) (Fin n) k) hp hxy

theorem Bi.relIndex_lat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m r : ℕ) :
    (Lat Z (m + r)).relIndex (Lat Z m) = (Lat Z r).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m,
    AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]

theorem Bi.relIndex_lat_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (m r : ℕ) :
    (Lat Z (m + r)).relIndex ((Lat Z m).map (conjA g)) = ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m]
  have hcomm : ((Lat Z 0).map (smulA (pi k ^ m))).map (conjA g) =
      ((Lat Z 0).map (conjA g)).map (smulA (pi k ^ m)) := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext1 x
    exact conjA_smulA g _ x
  rw [hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]
  have hid : (conjA g⁻¹).comp (conjA g) = AddMonoidHom.id _ := by
    ext1 x
    exact conjA_inv_conjA g x
  have := AddSubgroup.relIndex_map_map_of_injective (Lat Z r) ((Lat Z 0).map (conjA g))
    (conjA_injective g⁻¹)
  rw [AddSubgroup.map_map, hid, AddSubgroup.map_id] at this
  exact this.symm

theorem indexSym [CharZero k] : IndexSym (k := k) := by
  intro n Z hZ g hg
  obtain ⟨c0, hc01, hc0⟩ := exists_shift Z g hg
  obtain ⟨c1, hc1⟩ := core Z hZ g hg
  refine ⟨c0 + c1, fun m hm m' hm' => ?_⟩
  have h1m : 1 ≤ m := by omega
  obtain ⟨r, rfl⟩ : ∃ r, m' = m + r := ⟨m' - m, by omega⟩
  have hr : c1 ≤ r := by omega
  refine ⟨Lc_le Z g hg c0 hc0 h1m (by omega), ?_, ?_⟩
  · rw [relIndex_Lc_conj Z g hg c0 hc0 h1m (by omega) (by omega), relIndex_Lc Z h1m (by omega),
      Bi.relIndex_lat_conj, Bi.relIndex_lat]
    exact (hc1 r hr).1
  · rw [relIndex_Lc Z h1m (by omega), Bi.relIndex_lat]
    exact (hc1 r hr).2

end PositivityTheory.RgUd.T.Desc.SLT
