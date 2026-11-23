import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubrepFixedOfUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.PfBern.Props2

section General

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

theorem finite_orbit_of_isSmooth {ρ : Representation ℂ G X} (hρ : IsSmooth ρ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : X) : (Set.range fun k : K => ρ k w).Finite := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine IsLocallyConstant.range_finite ?_
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hc : Continuous fun y : K => (x : G)⁻¹ * (y : G) := continuous_const.mul continuous_subtype_val
  have hU : IsOpen ((fun y : K => (x : G)⁻¹ * (y : G)) ⁻¹' {g : G | ρ g w = w}) := (hρ w).preimage hc
  filter_upwards [hU.mem_nhds (by simp)] with y hy
  have hy' : ρ ((x : G)⁻¹ * (y : G)) w = w := hy
  calc ρ (y : G) w = ρ (x : G) (ρ ((x : G)⁻¹ * (y : G)) w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρ (x : G) w := by rw [hy']

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitSemisimple_hyp {N : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ (GL (Fin N) k) X} (hπ : IsAdmissible π) (v : X) :
    ∃ K : Subgroup (GL (Fin N) k), (∀ g ∈ K, π g v = v) ∧ FiniteDimensional ℂ (fixed π K) ∧
      ∀ w, (Set.range fun g : K => π g w).Finite := by
  have hU : {g : GL (Fin N) k | π g v = v} ∈ nhds (1 : GL (Fin N) k) :=
    (hπ.1 v).mem_nhds (by simp)
  obtain ⟨K, hKo, hKc, hKU⟩ := GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N _ hU
  exact ⟨K, fun g hg => hKU hg, hπ.2 K hKo hKc, finite_orbit_of_isSmooth hπ.1 K hKc⟩

theorem unitaryAdmissibleComplement_at (N : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (GL (Fin N) k) X) (hπ : IsAdmissible π) (hu : IsUnitarisable π)
    (S : Subrepresentation π) : ∃ T : Subrepresentation π, IsCompl S.toSubmodule T.toSubmodule := by
  obtain ⟨B, hs, hp, hi⟩ := hu
  have hdef : ∀ v, B.flip v v = 0 → v = 0 := fun v h => by
    by_contra hv
    have := hp v hv
    rw [LinearMap.flip_apply] at h
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hinv : ∀ g u v, B.flip (π g u) (π g v) = B.flip u v := fun g u v => by
    simp only [LinearMap.flip_apply, hi]
  let T : Subrepresentation π :=
    { toSubmodule :=
        { carrier := {w | ∀ z ∈ S.toSubmodule, B.flip z w = 0}
          add_mem' := fun {a b} ha hb z hz => by rw [map_add, ha z hz, hb z hz, add_zero]
          zero_mem' := fun z _ => by rw [map_zero]
          smul_mem' := fun c w hw z hz => by rw [map_smul, hw z hz, smul_zero] }
      apply_mem_toSubmodule := fun g w hw =>
        GlobalTheory.UnitarySemisimple.orth_stable π B.flip hinv S w hw g }
  refine ⟨T, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxS hxT
    exact hdef x (hxT x hxS)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj π B.flip hdef hinv
      (unitSemisimple_hyp hπ) S v
    have hvT : v - t ∈ T.toSubmodule := ht
    have := Submodule.add_mem_sup htS hvT
    rwa [add_sub_cancel] at this

end PositivityTheory.PfBern.Props2
