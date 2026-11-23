import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaPointEval
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ0 : Set.Ioo (0 : ℝ) 1}

def smallSubgroup (I : Set (Set.Ioc (0 : ℝ) ρ0)) (hI : I.Finite) (ε : Set.Ioc (0 : ℝ) ρ0 → ℝ)
    (hε : ∀ i, 0 < ε i) : OpenAddSubgroup (T.RobbaExt ρ0) where
  carrier := {x | ∀ i ∈ I, T.extNorm ρ0 i x < ε i}
  zero_mem' := fun i _ => by rw [T.extNorm_zero]; exact hε i
  add_mem' := fun {a b} ha hb i hi =>
    (T.extNorm_add_le i a b).trans_lt (max_lt (ha i hi) (hb i hi))
  neg_mem' := fun {a} ha i hi => by rw [T.extNorm_neg]; exact ha i hi
  isOpen' := by
    have : {x : T.RobbaExt ρ0 | ∀ i ∈ I, T.extNorm ρ0 i x < ε i} =
        ⋂ i ∈ I, {x | T.extNorm ρ0 i x < ε i} := by
      ext x; simp
    rw [this]
    exact hI.isOpen_biInter fun i _ => isOpen_lt (T.continuous_extNorm i) continuous_const

theorem exists_radii_of_mem_nhds_zero {U : Set (T.RobbaExt ρ0)} (hU : U ∈ 𝓝 (0 : T.RobbaExt ρ0)) :
    ∃ I : Set (Set.Ioc (0 : ℝ) ρ0), I.Finite ∧ ∃ ε : Set.Ioc (0 : ℝ) ρ0 → ℝ, (∀ i, 0 < ε i) ∧
      ∀ x : T.RobbaExt ρ0, (∀ i ∈ I, T.extNorm ρ0 i x < ε i) → x ∈ U := by
  obtain ⟨V, hV, hVU⟩ := UniformSpace.mem_nhds_iff.1 hU
  obtain ⟨I, hI, ε, hε, h⟩ := T.exists_radii_of_mem_uniformity hV
  refine ⟨I, hI, ε, hε, fun x hx => hVU ?_⟩
  refine h 0 x fun i hi => ?_
  rw [zero_sub, T.extNorm_neg]; exact hx i hi

instance instNonarchimedeanAddGroupRobbaExt : NonarchimedeanAddGroup (T.RobbaExt ρ0) where
  is_nonarchimedean U hU := by
    obtain ⟨I, hI, ε, hε, h⟩ := T.exists_radii_of_mem_nhds_zero hU
    exact ⟨T.smallSubgroup I hI ε hε, fun x hx => h x hx⟩

variable {T}

theorem HasSum.res {ι : Type*} {f : ι → T.RobbaExt ρ0} {s : T.RobbaExt ρ0} (hs : HasSum f s)
    {ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    HasSum (fun i => T.res h (f i)) (T.res h s) :=
  hs.map (T.res h) (T.continuous_res h)

theorem HasSum.extFrob (F : T.TeichFrob) {ι : Type*} {f : ι → T.RobbaExt ρ0} {s : T.RobbaExt ρ0}
    (hs : HasSum f s) : HasSum (fun i => F.extFrob ρ0 (f i)) (F.extFrob ρ0 s) :=
  hs.map (F.extFrob ρ0) (F.continuous_extFrob ρ0)

end TeichLift

end GroundTheory.PAdicHodge
