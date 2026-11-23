import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem lattice_basis_exists : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  intro l _ G _ _ LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI hfr : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let e0 := Module.Free.chooseBasis ↥(OL LL) ↥T.L.T
  let e := e0.reindex (Fintype.equivFin _)
  let v : Fin (Fintype.card (Module.Free.ChooseBasisIndex ↥(OL LL) ↥T.L.T)) → T.V := fun i => (e i : T.V)
  have hliO : LinearIndependent ↥(OL LL) v := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ↥LL.1 v := (LinearIndependent.iff_fractionRing ↥(OL LL) ↥LL.1).1 hliO

  have hexp : ∀ (x : T.V) (hx : x ∈ T.L.T), x = ∑ i, (((e.repr ⟨x, hx⟩ i : ↥(OL LL)) : ↥LL.1)) • v i := by
    intro x hx
    have h1 := e.sum_repr ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥T.L.T => (y : T.V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ↥LL.1 (e.repr ⟨x, hx⟩ i) (v i)).symm
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range v) := by
    rw [← T.L.span]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, Module.Basis.mk hli hsp, fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (e i).2
  · have h3 : (Module.Basis.mk hli hsp).repr x = fun j => (((e.repr ⟨x, hx⟩ j : ↥(OL LL)) : ↥LL.1)) := by
      conv_lhs => rw [hexp x hx]
      simp_rw [← Module.Basis.mk_apply hli hsp]
      exact (Module.Basis.mk hli hsp).repr_sum_self _
    rw [h3]
    exact (e.repr ⟨x, hx⟩ i).2

end GlobalTheory.BaseCoef
