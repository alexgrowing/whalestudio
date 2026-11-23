import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrBase
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.Imports

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime]

theorem fc_inv_mem {R F : Type*} [CommRing R] [Field F] (f : R →+* F) {u : R} (hu : IsUnit u) :
    (f u)⁻¹ ∈ f.range := by
  obtain ⟨v, rfl⟩ := hu
  exact ⟨↑v⁻¹, map_units_inv (f : R →* F) v⟩

theorem fc_isUnit_sub {F : Type*} [Field F] (S : Subring F) {x : F} (hx : x ∈ S) (hx' : x⁻¹ ∈ S) (h0 : x ≠ 0) :
    IsUnit (⟨x, hx⟩ : S) :=
  ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem fc_ι_c (a : ACris.ACris ℂ_[l] l) : period_ring_base.ι l (cB l a) = iC l a := Loc2.lift_mk₀ _ _ _ a

theorem fc_range_le : (period_ring_base.ι l).range ≤ Bcr l := by
  let f : ACris.ACris ℂ_[l] l →+* Bcr l := (iC l).codRestrict (Bcr l) (fun a => iC_mem_bcr a)
  have hl : IsUnit (f (l : ACris.ACris ℂ_[l] l)) := by
    have e : iC l (l : ACris.ACris ℂ_[l] l) = (l : BdR l) := map_natCast _ l
    have := fc_isUnit_sub (Bcr l) (x := iC l (l : ACris.ACris ℂ_[l] l)) (iC_mem_bcr _) (by rw [e]; exact linv_mem_bcr)
      (by rw [e]; exact l_ne)
    exact this
  have ht : IsUnit (f (tA l)) :=
    fc_isUnit_sub (Bcr l) (x := iC l (tA l)) (iC_mem_bcr _) tinv_mem_bcr DeRhamTwist.Twist.tQ_ne
  have hg : (Bcr l).subtype.comp (Loc2.lift f hl ht) = period_ring_base.ι l :=
    Loc2.hom_ext (fun x => by
      rw [RingHom.comp_apply, Loc2.lift_mk₀]
      exact (fc_ι_c x).symm)
  rintro _ ⟨x, rfl⟩
  rw [← hg]
  exact (Loc2.lift f hl ht x).2

theorem fc_bcr_le : Bcr l ≤ (period_ring_base.ι l).range := by
  have hb := period_ring_base.base l
  refine Subring.closure_le.2 ?_
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact ⟨_, fc_ι_c a⟩
  · have h := fc_inv_mem (period_ring_base.ι l) (period_ring_base.isUnit_l l)
    rwa [map_natCast] at h
  · have h := fc_inv_mem (period_ring_base.ι l) hb.t_unit
    rwa [hb.ι_t] at h

theorem fc_range : (period_ring_base.ι l).range = Bcr l := le_antisymm fc_range_le fc_bcr_le

theorem factsC : BcrisPeriodFacts := fun l _ K r => by
  have hb := period_ring_base.base l
  refine ⟨⟨fun a => fc_ι_c a, fun z => hb.ι_q z, hb.ι_inj, Loc2.isUnit_right _ _,
      ?_, fun z => hb.φ_q z, ?_, ?_, fun g z => hb.σ_q g.1 z, ?_⟩, fc_range⟩
  · intro a
    show φB l (cB l a) = cB l (ACris.phi ℂ_[l] l a)
    exact Loc2.map_mk₀ _ _ _ _ _ a
  · intro z
    show ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (IsPerfectoidField.padicIntToWitt l z)) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)
    rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]
  · intro g a
    show Formalism.Per6.σB g.1 (cB l a) = cB l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) a)
    exact Loc2.map_mk₀ _ _ _ _ _ a
  · intro g a
    show ACris.phi ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) a) =
      ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) (ACris.phi ℂ_[l] l a)
    rw [← ACris.gal_smul_def, ← ACris.gal_smul_def, ACris.phi_gal_smul]

end CrystallineSemistableComparison
