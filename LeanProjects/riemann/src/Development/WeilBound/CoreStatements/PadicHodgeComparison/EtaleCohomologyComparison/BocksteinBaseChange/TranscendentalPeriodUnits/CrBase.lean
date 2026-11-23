import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.Imports
import GroundTheory.PAdicHodge.BCrisNewton
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.BCrisEigenMaps
import GroundTheory.PAdicHodge.FontaineLemmaInvariants

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

section Abstract

variable {F : Type*} [Field F]

theorem eq_mul_inv_pow {x T L W : F} {n m : ℕ} (hT : T ≠ 0) (hL : L ≠ 0) (h : x * (T ^ n * L ^ m) = W) :
    x = W * T⁻¹ ^ n * L⁻¹ ^ m := by
  rw [← h, inv_pow, inv_pow]
  field_simp

end Abstract

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

local notation "ιB" => ACris.iotaB (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

set_option maxHeartbeats 1600000 in
theorem iotaB_padic (q : ℚ_[l]) :
    ιB (algebraMap ℚ_[l] (ACris.BCris (untilt_epsilon (p := l))) q) = qQ l q :=
  ACris.iotaB_algebraMap_padic_bdRPlus _ _ q

set_option maxHeartbeats 1600000 in
theorem iotaB_periodTCris : ιB (ACris.periodTCris (untilt_epsilon (p := l))) = tQ l :=
  ACris.iotaB_periodTCris _ _

set_option maxHeartbeats 1600000 in
theorem σD_iotaB (g : K.fixingSubgroup) (x : ACris.BCris (untilt_epsilon (p := l))) :
    σD g.1 (ιB x) = ιB (ACris.galB _ (IntermediateField.fixingSubgroupEquiv K g) x) :=
  (ACris.iotaB_galB _ _ (IntermediateField.fixingSubgroupEquiv K g) x).symm

set_option maxHeartbeats 1600000 in
theorem iotaB_acris (a : ACris.ACris ℂ_[l] l) :
    ιB (algebraMap (ACris.BCrisPlus ℂ_[l] l) (ACris.BCris (untilt_epsilon (p := l)))
      (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) a)) = iC l a :=
  (ACris.iotaB_algebraMap _ _ _).trans (congrArg _ (ACris.iotaPlus_algebraMap a))

theorem l_ne : ((l : BdR l)) ≠ 0 := by
  rw [← map_natCast (qQ l)]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem inv_mem_range {R F : Type*} [CommRing R] [Field F] (f : R →+* F) {u : R} (hu : IsUnit u) :
    (f u)⁻¹ ∈ f.range := by
  obtain ⟨v, rfl⟩ := hu
  exact ⟨↑v⁻¹, map_units_inv (f : R →* F) v⟩

set_option maxHeartbeats 1600000 in
theorem linv_mem_range : ((l : BdR l))⁻¹ ∈ (ιB).range := by
  have hu : IsUnit ((l : ACris.BCris (untilt_epsilon (p := l)))) := by
    have := (IsLocalization.Away.algebraMap_isUnit (S := ACris.BCrisPlus ℂ_[l] l)
      (l : ACris.ACris ℂ_[l] l)).map
      (algebraMap (ACris.BCrisPlus ℂ_[l] l) (ACris.BCris (untilt_epsilon (p := l))))
    rw [map_natCast] at this
    rwa [map_natCast] at this
  have h := inv_mem_range ιB hu
  rwa [map_natCast] at h

set_option maxHeartbeats 1600000 in
theorem tinv_mem_range : (tQ l)⁻¹ ∈ (ιB).range := by
  have h := inv_mem_range ιB (ACris.isUnit_periodTCris (untilt_epsilon (p := l)))
  rwa [iotaB_periodTCris] at h

theorem iC_mem_bcr (a : ACris.ACris ℂ_[l] l) : iC l a ∈ Bcr l :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem linv_mem_bcr : ((l : BdR l))⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inl rfl))

theorem tinv_mem_bcr : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

set_option maxHeartbeats 1600000 in
theorem range_le_bcr : (ιB).range ≤ Bcr l := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨w, n, m, h⟩ := exists_mul_eq_of_away_away (ACris.iota ℂ_[l] l) (ACris.iotaPlus ℂ_[l] l)
    (fun a => ACris.iotaPlus_algebraMap a) (algebraMap (BdRp l) (BdR l)) ιB
    (fun x => ACris.iotaB_algebraMap _ _ x) u
  have e1 : algebraMap (BdRp l) (BdR l) (ACris.iotaPlus ℂ_[l] l
      (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) (ACris.periodT (untilt_epsilon (p := l)))) ^ n *
      ACris.iota ℂ_[l] l (l : ACris.ACris ℂ_[l] l) ^ m) = tQ l ^ n * (l : BdR l) ^ m := by
    rw [ACris.iotaPlus_algebraMap, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    rfl
  rw [e1] at h
  rw [eq_mul_inv_pow DeRhamTwist.Twist.tQ_ne l_ne h]
  exact mul_mem (mul_mem (iC_mem_bcr w) (pow_mem tinv_mem_bcr _)) (pow_mem linv_mem_bcr _)

set_option maxHeartbeats 1600000 in
theorem bcr_eq : Bcr l = (ιB).range := by
  refine le_antisymm (Subring.closure_le.2 ?_) range_le_bcr
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact ⟨_, iotaB_acris a⟩
  · exact linv_mem_range
  · exact tinv_mem_range

theorem q_mem_bcr (z : ℚ_[l]) : qQ l z ∈ Bcr l := by
  rw [bcr_eq]
  exact ⟨_, iotaB_padic z⟩

theorem bcr_stab (g : K.fixingSubgroup) (x : BdR l) (hx : x ∈ Bcr l) : σD g.1 x ∈ Bcr l := by
  rw [bcr_eq] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, (σD_iotaB g y).symm⟩

end CrystallineSemistableComparison
