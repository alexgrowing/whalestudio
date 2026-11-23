import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrBase

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

local notation "ιB" => ACris.iotaB (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem per_σ (g : K.fixingSubgroup) (x : BdR l) : (per l K).σ g x = σD g.1 x := rfl

theorem fix_of_σD {x : BdR l} (h : ∀ g : K.fixingSubgroup, σD g.1 x = x) (σ : Gal(PadicAlgCl l/K)) : σ • x = x := by
  have e := h ((IntermediateField.fixingSubgroupEquiv K).symm σ)
  have e2 : σD ((IntermediateField.fixingSubgroupEquiv K).symm σ).1 x =
      galBdRField (IntermediateField.fixingSubgroupEquiv K ((IntermediateField.fixingSubgroupEquiv K).symm σ)) x := rfl
  rw [e2, MulEquiv.apply_symm_apply] at e
  exact e

set_option maxHeartbeats 1600000 in
theorem bcr_frac [FiniteDimensional ℚ_[l] K] (x : BdR l) (hx : x ∈ Bcr l) (y : BdR l) (hy : y ∈ Bcr l) (w : BdR l)
    (hwy : w * y = x) (hy0 : y ≠ 0) (hw : ∀ g : K.fixingSubgroup, σD g.1 w = w) : w ∈ Bcr l := by
  rw [bcr_eq] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hwF : w ∈ ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one := by
    rw [eq_div_of_mul_eq hy0 hwy]
    exact div_mem (ACris.iotaB_mem_fracBCris _ _ a) (ACris.iotaB_mem_fracBCris _ _ b)
  obtain ⟨k, hk, rfl⟩ := ACris.fracBCris_fixed (K := K) _ _ hwF (fix_of_σD hw)
  obtain ⟨c, -, hc⟩ := ACris.exists_bCris_fixed (K := K) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one hk
  exact ⟨c, hc⟩

theorem all_of_σD {P : BdR l → Prop} {x : BdR l} (h : ∀ g : K.fixingSubgroup, P (σD g.1 x))
    (σ : Gal(PadicAlgCl l/K)) : P (σ • x) := by
  have e := h ((IntermediateField.fixingSubgroupEquiv K).symm σ)
  have e2 : σD ((IntermediateField.fixingSubgroupEquiv K).symm σ).1 x =
      galBdRField (IntermediateField.fixingSubgroupEquiv K ((IntermediateField.fixingSubgroupEquiv K).symm σ)) x := rfl
  rw [e2, MulEquiv.apply_symm_apply] at e
  exact e

set_option maxHeartbeats 1600000 in
theorem galB_eigen (b : ACris.BCris (untilt_epsilon (p := l)))
    (he : ∀ σ : Gal(PadicAlgCl l/K), ∃ z : ℚ_[l], σ • ιB b = qQ l z * ιB b) (σ : Gal(PadicAlgCl l/K)) :
    ∃ q : ℚ_[l], ACris.galB (untilt_epsilon (p := l)) σ b =
      algebraMap ℚ_[l] (ACris.BCris (untilt_epsilon (p := l))) q * b := by
  obtain ⟨z, hz⟩ := he σ
  have hz' : ιB (ACris.galB (untilt_epsilon (p := l)) σ b) =
      ιB (algebraMap ℚ_[l] (ACris.BCris (untilt_epsilon (p := l))) z * b) :=
    ((ACris.iotaB_galB _ _ σ b).trans hz).trans ((map_mul ιB _ b).trans (congrArg (· * ιB b) (iotaB_padic z))).symm
  exact ⟨z, ACris.iotaB_injective (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one hz'⟩

set_option maxHeartbeats 1600000 in
theorem bcr_eig [FiniteDimensional ℚ_[l] K] (x : BdR l) (hx : x ∈ Bcr l) (hx0 : x ≠ 0)
    (he : ∀ g : K.fixingSubgroup, ∃ z : ℚ_[l], σD g.1 x = qQ l z * x) : ∃ y ∈ Bcr l, x * y = 1 := by
  rw [bcr_eq] at hx
  obtain ⟨b, rfl⟩ := hx
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (map_zero _)
  obtain ⟨u, hu⟩ := ACris.isUnit_of_galB_eigen (K := K) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one hb0
    (galB_eigen b (all_of_σD (P := fun y => ∃ z : ℚ_[l], y = qQ l z * ιB b) he))
  refine ⟨ιB ↑u⁻¹, ?_, ?_⟩
  · rw [bcr_eq]
    exact ⟨_, rfl⟩
  · rw [← hu, ← map_mul, Units.mul_inv, map_one]

theorem regCr : BcrisRegularPeriodRing := by
  intro l _ K _
  exact
    { q_mem := q_mem_bcr
      stab := fun g x hx => bcr_stab g x hx
      frac := fun x hx y hy w hwy hy0 hw => bcr_frac x hx y hy w hwy hy0 hw
      eig := fun x hx hx0 he => bcr_eig x hx hx0 he }

end CrystallineSemistableComparison
