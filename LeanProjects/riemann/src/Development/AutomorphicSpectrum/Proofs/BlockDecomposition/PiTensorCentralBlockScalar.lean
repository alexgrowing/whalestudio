import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCScalar

theorem piTensor_zj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL k) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  intro k _ _ _ _ h x t c hc j v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have hf : ∀ a, (x a).rep (Zl.JC.zj (fun a => (x a).1) t j a) (f a)
        = (if a ≤ j then c a else 1) • f a := by
      intro a
      by_cases ha : a ≤ j
      · simp only [Zl.JC.zj, if_pos ha]
        exact hc a (f a)
      · simp [Zl.JC.zj, if_neg ha]
    simp only [hf]
    rw [MultilinearMap.map_smul_univ, Finset.prod_filter]
  | add a b ha hb => rw [map_add, ha, hb, smul_add]

end GlobalTheory.CompanionTheory.JCScalar
