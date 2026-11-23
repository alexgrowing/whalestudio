import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GluedExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowsMassOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AnisotropicComplementDefinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassHolds

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem row_lattice_mass : RowsMass := by
  intro D u u' _ F0 what₂ hrows
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  obtain ⟨hd, hk⟩ := anisotropic_complement_definite D u F0
  have hGH : GlueHyp D.host.E D.host.F (hWb D F0) (zbar D F0) (D.mem u).A.T :=
    ⟨hK, hF, hWb_isSymm D F0, hWb_zbar D F0, (D.mem u).A.T_prime.pos, hd⟩
  have hrl : ∀ Λ ∈ what₂, IsRowLat D F0 Λ := hrows.1
  have hinj : Set.InjOn (Mof D F0) (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)) := by
    intro Λ₁ h₁ Λ₂ h₂ he
    obtain ⟨γ, hγ, hγe⟩ := (row_class_holds D u F0 Λ₁ Λ₂ (hrl Λ₁ h₁) (hrl Λ₂ h₂)).2
      ⟨1, one_mem_hz D _ _, by rw [gmap_one' D, he]⟩
    obtain ⟨Λ', _, hu⟩ := hrows.2 Λ₂ (hrl Λ₂ h₂)
    have e1 := hu Λ₁ ⟨h₁, γ, hγ, hγe⟩
    have e2 := hu Λ₂ ⟨h₂, 1, one_mem_stabF D F0, gmap_one' D Λ₂⟩
    rw [e1, e2]
  have hreps : IsHzReps (hWb D F0) (zbar D F0) (what₂.image (Mof D F0)) := by
    refine ⟨fun M hM => ?_, fun M hM => ?_⟩
    · obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hM
      exact row_lattice_mass_holds D u F0 Λ (hrl Λ hΛ)
    · obtain ⟨Λ, hΛ, rfl⟩ := row_surjective D u F0 M hM
      obtain ⟨Λ', ⟨hΛ'm, γ, hγ, hγΛ'⟩, hu⟩ := hrows.2 Λ hΛ
      obtain ⟨σ, hσ, hσM⟩ := (row_class_holds D u F0 Λ' Λ (hrl Λ' hΛ'm) hΛ).1 ⟨γ, hγ, hγΛ'⟩
      refine ⟨Mof D F0 Λ', ⟨Finset.mem_image_of_mem _ hΛ'm, σ, hσ, hσM⟩, ?_⟩
      rintro M'' ⟨hM'', σ', hσ', hσ'M⟩
      obtain ⟨Λ'', hΛ''m, rfl⟩ := Finset.mem_image.1 hM''
      obtain ⟨γ'', hγ'', hγ''Λ⟩ := (row_class_holds D u F0 Λ'' Λ (hrl Λ'' hΛ''m) hΛ).2 ⟨σ', hσ', hσ'M⟩
      rw [hu Λ'' ⟨hΛ''m, γ'', hγ'', hγ''Λ⟩]
  have hk2 : 2 ≤ finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) := by
    rw [hk]
    have := D.R.m_add_three_le_k
    omega
  have hne : ∃ M, IsGlueLat (hWb D F0) (zbar D F0) M :=
    GluedLatticeMass.glued_exists hGH hk2 ⟨Mof D F0 (VS D).L0, RowMPf.Mof_isLattice D F0 _ (VS D).standardTuple_isLattice,
      RowMPf.Mof_unimod D F0 _ (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular⟩
  have e := GluedLatticeMass.glued_lattice_mass_formula hGH (by omega) hne hreps
  rw [hk] at e
  rw [← e, Finset.sum_image hinj]
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_congr rfl fun Λ hΛ => ?_
  unfold wRow
  rw [row_weight_formula D u F0 Λ (hrl Λ hΛ)]

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
example : Formalism.L2.SG.Pf.Cnt.RowsMass := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass
