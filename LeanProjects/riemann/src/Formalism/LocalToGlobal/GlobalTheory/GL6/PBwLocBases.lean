import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfSubIntegral
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

variable (D : D7) (u : D.what₂.Word)

private theorem isLattice_map_restrictScalars_linearEquiv {K R V W : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (e : V ≃ₗ[K] W) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (L.map ((e : V →ₗ[K] W).restrictScalars R)) := by
  obtain ⟨hfg, hsp⟩ := hL
  refine ⟨hfg.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top,
    LinearEquiv.range]

theorem bwB_clsCrd_lat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule.IsLattice D.host.E (clsCrd D u i hi c) := by
  have hL : Submodule.IsLattice D.host.E (D.clsLat u i c) := by
    first
      | exact D.clsLat_lat u i c
      | exact D.clsLat_isLat u i c
      | exact D.clsLat_isLattice u i c
      | exact D.clsLat_lattice u i c
      | exact (D.clsLat_spec u i c).1
      | exact D.clsLat_spec u i c
      | exact inferInstance
  unfold clsCrd
  exact isLattice_map_restrictScalars_linearEquiv _ _ hL

theorem bwB_gramN_det (i : ℕ) (hi : i ≤ D.R.m) : IsUnit (gramN D i hi).det := by
  letI := D.host.cmStar
  unfold gramN
  rw [Matrix.det_reindex_self, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfa : ∀ a, (D.sp.X i).hT ((D.sp.X i).frame a) (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro a
    have h := congrFun hv a
    have e : Matrix.mulVec (D.sp.X i).gram v a =
        ∑ b, (D.sp.X i).hT ((D.sp.X i).frame a) ((D.sp.X i).frame b) * v b := rfl
    rw [e] at h
    simp only [map_sum, map_smul, smul_eq_mul]
    simpa [mul_comm] using h
  have hy : ∀ x, (D.sp.X i).hT x (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro x
    have h0 : (D.sp.X i).hT.flip (∑ b, v b • (D.sp.X i).frame b) = 0 :=
      (D.sp.X i).frame.ext (fun a => by simpa using hfa a)
    simpa using congrArg (fun f => f x) h0
  have hy0 := (D.sp.X i).nondeg.2 _ hy
  have hz := Fintype.linearIndependent_iff.mp (D.sp.X i).frame.linearIndependent v hy0
  exact hv0 (funext hz)

theorem local_bases_exist_of_compatible_forms (Tt : FormsTied D u) : BwLocBases D u Tt := by
  haveI : Fact (Nat.Prime (D.mem u).A.T) := ⟨(D.mem u).A.T_prime⟩
  intro i hi c
  have hL : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  obtain ⟨_, hspL⟩ := id hL
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (bwB_gramN_det D i hi) _ hL
  obtain ⟨d1, hd1, hle1⟩ := LocB.exists_le_bnd _ hL
  have hsp : Submodule.span D.host.E ((Ld D u i hi c : Submodule _ _) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ :=
    LocB.dual_span _ _ _ hL
  have hfg : (Ld D u i hi c).FG := by
    clear hle1 hd1 hsp hspL
    have h0 := LocB.fg_of_le_bnd hd hle
    unfold Ld dualL at *
    convert h0 using 3
  refine ⟨LocB.exists_isLocBasis (D.mem u).A.T _ (Ld D u i hi c) hfg hsp, fun v => ?_⟩
  have hle2 : Lk Tt.atT i hi v c ≤ LocB.bnd (d1 * d) := by
    refine sup_le (hle1.trans ?_) (Submodule.smul_le_right.trans (hle.trans (LocB.bnd_mono d d1)))
    rw [mul_comm]
    exact LocB.bnd_mono d1 d
  have hspK : Submodule.span D.host.E ((Lk Tt.atT i hi v c : Submodule _ _) :
      Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← hspL]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have hfgK : (Lk Tt.atT i hi v c).FG := LocB.fg_of_le_bnd (mul_ne_zero hd1 hd) hle2
  exact LocB.exists_isLocBasis (D.mem u).A.T _ (Lk Tt.atT i hi v c) hfgK hspK

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
