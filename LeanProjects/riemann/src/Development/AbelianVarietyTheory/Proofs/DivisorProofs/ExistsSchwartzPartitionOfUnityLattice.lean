import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothPeriodicPartitionOfUnity
open scoped ContDiff Topology

namespace GlobalTheory.LatticeSumOne

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_radius (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ R : ℝ, ∀ x : V, ∃ l : Λ, ‖x + l‖ ≤ R := by
  obtain ⟨t, ht⟩ := GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun k : V => {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1})
    (fun k => by
      have : {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1} =
          ⋃ l : Λ, (fun z : V => z + l) ⁻¹' Metric.ball k 1 := by
        ext z; simp
      rw [this]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (by fun_prop))
    (fun k l z hz => by
      obtain ⟨m, hm⟩ := hz
      refine ⟨m - l, ?_⟩
      simpa [add_sub_cancel, add_assoc, sub_eq_add_neg] using hm)
    (fun z => ⟨z, 0, by simp⟩)
  refine ⟨1 + ∑ k ∈ t, ‖k‖, fun x => ?_⟩
  obtain ⟨k, hk, l, hl⟩ := ht x
  refine ⟨l, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hl
  have h1 : ‖k‖ ≤ ∑ k ∈ t, ‖k‖ := Finset.single_le_sum (f := fun k => ‖k‖) (fun _ _ => norm_nonneg _) hk
  calc ‖x + l‖ = ‖(x + l - k) + k‖ := by abel_nf
    _ ≤ ‖x + l - k‖ + ‖k‖ := norm_add_le _ _
    _ ≤ 1 + ∑ k ∈ t, ‖k‖ := by linarith

theorem exists_schwartz_lattice_sum_one (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  obtain ⟨R, hR⟩ := exists_radius Λ
  set R' : ℝ := max R 1 with hR'
  let φ : ContDiffBump (0 : V) := ⟨R', R' + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  have hφc : HasCompactSupport (φ : V → ℝ) := φ.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (φ : V → ℝ) := φ.contDiff
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => φ.nonneg
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ (φ : V → ℝ) hφc
  set S : V → ℝ := fun z => ∑ᶠ l : Λ, φ (z + l) with hSdef
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : Λ) (z : V) => φ (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSper : ∀ (l : Λ) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hR z
    have h1 := single_le_finsum (f := fun m : Λ => φ (z + m)) l (hlf.point_finite z)
      (fun m => hφ0 _)
    have h2 : φ (z + l) = 1 := φ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hl.trans (le_max_left _ _))
    have : 1 ≤ S z := by rw [← h2]; exact h1
    linarith
  set g : V → ℂ := fun z => ((φ z * (S z)⁻¹ : ℝ) : ℂ) with hgdef
  have hgc : HasCompactSupport g := by
    have : HasCompactSupport (fun z => φ z * (S z)⁻¹) := hφc.mul_right
    exact this.comp_left (g := Complex.ofReal) (by simp)
  have hgs : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp (hφs.mul (hSs.inv fun z => (hSpos z).ne'))
  refine ⟨hgc.toSchwartzMap hgs, hgc, fun x => ?_⟩
  have hfin := hlf.point_finite x
  have hval : ∀ l : Λ, (hgc.toSchwartzMap hgs) (x + l) = ((φ (x + l) : ℝ) : ℂ) * ((S x)⁻¹ : ℝ) := by
    intro l
    show g (x + l) = _
    simp only [hgdef, hSper, Complex.ofReal_mul]
  simp_rw [hval]
  have hsum : HasSum (fun l : Λ => ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ))
      (∑ l ∈ hfin.toFinset, ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero fun l hl => by
      have : φ (x + l) = 0 := by
        by_contra hne
        exact hl (hfin.mem_toFinset.2 hne)
      simp [this]
  convert hsum using 1
  have hS : S x = ∑ l ∈ hfin.toFinset, φ (x + l) :=
    finsum_eq_sum_of_support_subset (fun l : Λ => φ (x + l)) (fun l hl => hfin.mem_toFinset.2 hl)
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← hS, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (hSpos x).ne', Complex.ofReal_one]

end GlobalTheory.LatticeSumOne

namespace GlobalTheory

theorem exists_schwartz_hasCompactSupport_latticeTranslates_sum_one :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  intro V _ _ _ Λ _ _
  exact LatticeSumOne.exists_schwartz_lattice_sum_one Λ

end GlobalTheory
