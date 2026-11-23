import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.CoveringRadius2

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

theorem qt_finrank (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    Module.finrank ℚ E = 2 * Formalism.HermitianLatticesTheory.fDeg E := by
  have := h.1
  have h1 := NumberField.IsTotallyComplex.finrank E
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem qt_bound_eq (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) (C : ℝ) :
    (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E =
      (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  rw [qt_finrank E h]
  push_cast
  rfl

theorem residue_admitted_of_known (hQ : Formalism.HermitianLatticeCounting.S7.DedekindZetaResidueBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C := by
  obtain ⟨C, hC, h⟩ := hQ
  refine ⟨C, hC, fun D E _ _ _ hE => ⟨dedekindZeta_residue E, tendsto_sub_one_mul_dedekindZeta_nhdsGT E, ?_⟩⟩
  rw [abs_of_pos (dedekindZeta_residue_pos E), ← qt_bound_eq E hE C]
  refine h E ?_
  rw [qt_finrank E hE]
  have : 0 < Formalism.HermitianLatticesTheory.fDeg E := Fintype.card_pos
  omega

theorem dedekind_residue_le_of_admitted (D : Formalism.BasicNotions.D7) (C : ℝ) (h : adm7 D C) (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    dedekindZeta_residue E ≤
      (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  obtain ⟨r, hr, hb⟩ := h E hE
  have h1 := tendsto_nhds_unique hr (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  have h2 : r = dedekindZeta_residue E := by exact_mod_cast h1
  rw [← h2]
  exact le_trans (le_abs_self r) hb

section Cover

variable {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L] [IsZLattice ℝ L]

def qt_basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ (EuclideanSpace ℝ (Fin N)) :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

theorem qt_basis_span : Submodule.span ℤ (Set.range (qt_basis L)) = L :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L

theorem qt_bdd : BddAbove (Set.range fun x : EuclideanSpace ℝ (Fin N) => Metric.infDist x (L : Set _)) := by
  refine ⟨∑ i, ‖qt_basis L i‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmem : ((ZSpan.floor (qt_basis L) x : Submodule.span ℤ (Set.range (qt_basis L))) : EuclideanSpace ℝ (Fin N)) ∈
      (L : Set _) := by
    exact (qt_basis_span L).le (ZSpan.floor (qt_basis L) x).2
  refine le_trans (Metric.infDist_le_dist_of_mem hmem) ?_
  rw [dist_eq_norm]
  exact ZSpan.norm_fract_le (qt_basis L) x

theorem qt_dual_ne (hN : 0 < N) : ∃ y ∈ dualLat L, y ≠ 0 := by
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ L) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    have h0 := Module.finrank_eq_card_basis (qt_basis L)
    simp at h0
    omega
  obtain ⟨i⟩ := hne
  set ℓ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((qt_basis L).coord i) with hℓ
  set y := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm ℓ with hy
  have hin : ∀ v, inner ℝ y v = (qt_basis L).coord i v := fun v => by
    rw [hy, InnerProductSpace.toDual_symm_apply]; rfl
  refine ⟨y, fun x hx => ?_, fun h0 => ?_⟩
  · rw [← qt_basis_span L] at hx
    have := ((qt_basis L).mem_span_iff_repr_mem ℤ x).1 hx i
    obtain ⟨z, hz⟩ := this
    refine ⟨z, ?_⟩
    rw [real_inner_comm, hin]
    simpa using hz.symm
  · have := hin (qt_basis L i)
    rw [h0, inner_zero_left] at this
    simp at this

theorem qt_cover (h5 : covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2)
    (κ : ℝ) (hκ : 0 < κ) (hd : ∀ y ∈ dualLat L, y ≠ 0 → κ ≤ ‖y‖) (x : EuclideanSpace ℝ (Fin N)) :
    ∃ y ∈ L, ‖x - y‖ ≤ (N : ℝ) / (2 * κ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hcl : IsClosed (L : Set (EuclideanSpace ℝ (Fin N))) := by
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  obtain ⟨y, hy, hxy⟩ := hcl.exists_infDist_eq_dist ⟨0, zero_mem L⟩ x
  refine ⟨y, hy, ?_⟩
  rw [← dist_eq_norm, ← hxy]
  have h1 : Metric.infDist x (L : Set _) ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N))) :=
    le_ciSup (qt_bdd L) x
  have h0 : 0 ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N))) := le_trans Metric.infDist_nonneg h1
  have h2 : κ ≤ firstMin (dualLat L) := by
    obtain ⟨y0, hy0, hy0'⟩ := qt_dual_ne L hN
    refine le_csInf ⟨‖y0‖, y0, hy0, hy0', rfl⟩ ?_
    rintro r ⟨z, hz, hz', rfl⟩
    exact hd z hz hz'
  have h3 : covRad (L : Set (EuclideanSpace ℝ (Fin N))) * κ ≤ (N : ℝ) / 2 :=
    le_trans (mul_le_mul_of_nonneg_left h2 h0) h5
  refine le_trans h1 ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end Cover

theorem cover_radius_of_admitted (D : Formalism.BasicNotions.D7) (h : adm5 D) : Formalism.HermitianLatticeCounting.S7.CoveringRadius2 := by
  intro V _ _ _ M hM hspan κ hκ hd x
  set N := Module.finrank ℝ V with hN
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ V).repr
  let eZ : V →ₗ[ℤ] EuclideanSpace ℝ (Fin N) := (e.toLinearEquiv.toLinearMap).restrictScalars ℤ
  have heZ : ∀ v, eZ v = e v := fun v => rfl
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin N)) := M.map eZ
  have hback : ∀ y : L, e.symm (y : EuclideanSpace ℝ (Fin N)) ∈ M := by
    rintro ⟨y, v, hv, rfl⟩
    simpa [heZ] using hv
  have hdisc : DiscreteTopology L := by
    have := hM
    refine DiscreteTopology.of_continuous_injective (f := fun y : L => (⟨e.symm y, hback y⟩ : M)) ?_ ?_
    · exact Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (e.symm.injective this)
  have hlat : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have h1 : ((L : Submodule ℤ _) : Set (EuclideanSpace ℝ (Fin N))) = e.toLinearEquiv.toLinearMap '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have h5 := h N L hlat
  have hd' : ∀ y ∈ dualLat L, y ≠ 0 → κ ≤ ‖y‖ := by
    intro y hy hy0
    have h1 : e.symm y ∈ Formalism.HadamardInequality.zdual M := by
      intro v hv
      obtain ⟨z, hz⟩ := hy (e v) ⟨v, hv, rfl⟩
      refine ⟨z, ?_⟩
      rw [← hz, ← e.inner_map_map, e.apply_symm_apply]
    have h2 : e.symm y ≠ 0 := fun h0 => hy0 (by simpa using congrArg e h0)
    have := hd _ h1 h2
    rwa [e.symm.norm_map] at this
  obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := qt_cover L h5 κ hκ hd' (e x)
  refine ⟨v, hv, ?_⟩
  rw [heZ, ← map_sub, e.norm_map] at hy
  exact hy

theorem admitted_of_cover_radius (D : Formalism.BasicNotions.D7) (h : Formalism.HermitianLatticeCounting.S7.CoveringRadius2) : adm5 D := by
  intro N L hdisc hlat
  have hnn : 0 ≤ firstMin (dualLat L) := by
    refine Real.sInf_nonneg ?_
    rintro r ⟨y, -, -, rfl⟩
    exact norm_nonneg _
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  have hd : ∀ y ∈ Formalism.HadamardInequality.zdual L, y ≠ 0 → firstMin (dualLat L) ≤ ‖y‖ := by
    intro y hy hy0
    refine csInf_le ⟨0, ?_⟩ ⟨y, hy, hy0, rfl⟩
    rintro r ⟨z, -, -, rfl⟩
    exact norm_nonneg _
  have hc : covRad (L : Set (EuclideanSpace ℝ (Fin N))) ≤ (N : ℝ) / (2 * firstMin (dualLat L)) := by
    refine ciSup_le fun x => ?_
    obtain ⟨y, hy, hxy⟩ := h (EuclideanSpace ℝ (Fin N)) L hdisc hlat.span_top _ hpos hd x
    refine le_trans (Metric.infDist_le_dist_of_mem hy) ?_
    rw [dist_eq_norm]
    simpa using hxy
  calc covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L)
      ≤ (N : ℝ) / (2 * firstMin (dualLat L)) * firstMin (dualLat L) := mul_le_mul_of_nonneg_right hc hnn
    _ = (N : ℝ) / 2 := by field_simp

theorem admitted_iff_cover_radius (D : Formalism.BasicNotions.D7) : adm5 D ↔ Formalism.HermitianLatticeCounting.S7.CoveringRadius2 :=
  ⟨cover_radius_of_admitted D, admitted_of_cover_radius D⟩

end Formalism.MainNotions.LeviCoordinates
