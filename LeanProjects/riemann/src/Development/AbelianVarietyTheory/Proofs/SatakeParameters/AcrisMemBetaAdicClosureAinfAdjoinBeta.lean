import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris_mem_clos : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  intro l _ j hj ϖ hS hF x n
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x N
  obtain ⟨a, ha⟩ := hN z
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) ((s : Per.AinfP l) + algebraMap (Per.Ainf l) (Per.AinfP l) a),
    ⟨_, add_mem (hS s) (Subalgebra.algebraMap_mem _ a), rfl⟩, ?_⟩
  rw [← Ideal.mem_span_singleton, ← hF, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, map_add, map_add, map_mul, map_pow,
    map_natCast, hj.on0, ev_algebraMap, ev_algebraMap]
  rw [ha, map_add]
  ring

end GlobalTheory.Pst.StLat
