import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.KilledHolds
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
import ReciprocityTheory.GroupCohomology.ProdHolds
import ReciprocityTheory.GroupCohomology.EqZeroOfLe
import ReciprocityTheory.GroupCohomology.MemCoboundariesOfCocycleProcyclic

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Function

universe u

namespace ProcyclicCohomology

theorem length_ker_eq_coker {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] V) (h : IsFiniteLength R V) :
    Module.length R (LinearMap.ker f) = Module.length R (V ⧸ LinearMap.range f) := by
  have h1 : Module.length R V = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.injective_subtype _)
      f.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R V = Module.length R (LinearMap.range f) + Module.length R (V ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have hVt : Module.length R V ≠ ⊤ := Module.length_ne_top_iff.2 h
  have hL : Module.length R (LinearMap.range f) ≠ ⊤ := fun h' => hVt (by rw [h1, h', add_top])
  rw [h1, add_comm (Module.length R (LinearMap.range f))] at h2
  exact (WithTop.add_right_cancel hL h2)

end ProcyclicCohomology

theorem zHat_holds : ZHatStatement.{u} := by
  intro R _ G _ _ _ _ _ _ s hG M _ htor
  have hs := hG.1
  have hidx := hG.2
  have hc := ProcyclicCohomology.comm_of_dense hs
  have hA := ProcyclicCohomology.model_comparison_degree_zero_bijective M hc hs hidx htor
  have hH2 : ∀ (M' : TRep R G) [DiscreteTopology M'.V], (∀ m : M'.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
      Subsingleton (M'.H 2) := by
    intro M' _ ht
    obtain ⟨-, -, -, e2, -⟩ := low_holds R G M'
    have := ProcyclicCohomology.subsingleton_H2_of_procyclic_of_torsion M' hc hs hidx ht
    exact e2.toEquiv.subsingleton
  have hB : ∀ n, 1 < n → Subsingleton (M.H n) := fun n hn =>
    shift_holds R G 2 hH2 M htor n hn
  refine ⟨hA, hB, fun hM => ?_⟩
  obtain ⟨-, ⟨e0, -⟩, ⟨e1, -⟩, -⟩ := low_holds R G M
  obtain ⟨eA, -⟩ := hA
  set f := M.rho s - LinearMap.id
  have hH0 : H0 M.rho = LinearMap.ker f := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, LinearMap.mem_ker]
    constructor
    · intro h; simp [f, h s]
    · intro h g
      have h' : M.rho s m = m := by
        have := h
        simp only [f, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
        exact this
      have := ProcyclicCohomology.cocycle_eq_of_apply M hs 0 (Z1 M.rho).zero_mem m (by simp [h']) g
      rw [Pi.zero_apply, eq_comm, sub_eq_zero] at this
      exact this
  have fl0 : IsFiniteLength R (M.H 0) :=
    (hM.of_injective (Submodule.injective_subtype (H0 M.rho))).of_injective e0.injective
  have fl1 : IsFiniteLength R (M.H 1) :=
    (hM.of_surjective (Submodule.mkQ_surjective (LinearMap.range f))).of_injective
      (e1.trans eA).injective
  have hfl : ∀ n, IsFiniteLength R (M.H n) := by
    intro n
    rcases n with _ | _ | n
    · exact fl0
    · exact fl1
    · have := hB (n + 2) (by omega); exact .of_subsingleton
  refine ⟨⟨hfl, hB⟩, ?_⟩
  have l0 : Module.length R (M.H 0) = Module.length R (LinearMap.ker f) := by
    rw [e0.length_eq, hH0]
  have l1 : Module.length R (M.H 1) = Module.length R (M.V ⧸ LinearMap.range f) :=
    (e1.trans eA).length_eq
  have l01 : Module.length R (M.H 0) = Module.length R (M.H 1) := by
    rw [l0, l1, ProcyclicCohomology.length_ker_eq_coker f hM]
  simp only [Cx.chi, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, one_mul,
    neg_one_mul, zero_add]
  rw [show Module.length R (M.coch.H 0) = Module.length R (M.coch.H 1) from l01]
  ring

end ReciprocityTheory.Coh
