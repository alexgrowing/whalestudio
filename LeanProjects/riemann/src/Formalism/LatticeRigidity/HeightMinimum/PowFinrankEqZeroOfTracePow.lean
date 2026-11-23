import Formalism.LatticeRigidity.StatementD
import Mathlib

namespace Formalism.SA.P

open Matrix Polynomial
open scoped ComplexOrder

section TracePow

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem finite_eig (f : Module.End K V) : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := by
  first
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.iSupIndep_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt
      (Module.End.independent_maxGenEigenspace f)
  | exact (Module.End.independent_maxGenEigenspace f).finite_ne_bot
  | exact (Module.End.iSupIndep_maxGenEigenspace f).finite_ne_bot

theorem trace_pow_restrict_maxGen (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ,
      (((f.restrict h1) ^ m) z : V) = (f ^ m) z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      first
      | rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      | rw [pow_succ', LinearMap.mul_apply, pow_succ', LinearMap.mul_apply, ← ih]
      rfl
  have hg : (f ^ j).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) =
      (f.restrict h1) ^ j :=
    LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)
  rw [hg]
  have hxy : IsNilpotent (f.restrict h1 -
      algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
    convert Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1
    refine LinearMap.ext fun z => Subtype.ext ?_
    first
    | rfl
    | simp [LinearMap.restrict_apply]
    | simp
  generalize f.restrict h1 = x at hxy ⊢
  have hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) :=
    (Algebra.commutes μ x).symm
  have hnil : IsNilpotent
      (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) := by
    rw [← hc.geom_sum₂_mul]
    have hcomm : Commute (∑ i ∈ Finset.range j, x ^ i *
        (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i))
        (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      refine Commute.sub_right ?_ ?_
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
        | exact Commute.sum_left fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
        | exact Commute.sum_left fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
    first
    | exact hcomm.isNilpotent_mul_left hxy
    | exact hcomm.isNilpotent_mul_right hxy
    | exact hcomm.symm.isNilpotent_mul_left hxy
    | exact hcomm.symm.isNilpotent_mul_right hxy
  have h0 : LinearMap.trace K _ (x ^ j -
      (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0 := by
    first
    | exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    | exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))),
    Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]

theorem trace_pow_eq_sum (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  classical
  have htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤ := by
    refine eq_top_iff.mpr ?_
    first
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top (f := f)]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.maxGenEigenspace μ = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ)
        μ (by simpa using hμ) le_rfl
  have hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K)) := by
    first
    | exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective
    | exact (Module.End.iSupIndep_maxGenEigenspace f).comp Subtype.val_injective
  have hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm
  have htr := LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j)
    (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))
  exact htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))

end TracePow

section Lattice

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Lattice

end Formalism.SA.P
