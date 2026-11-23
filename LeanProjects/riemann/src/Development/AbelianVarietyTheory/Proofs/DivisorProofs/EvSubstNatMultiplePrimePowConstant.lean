import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvResCounitCompatStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem pullTwo_mulBy_pow_self {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (t : G.A n ⊗[O] G.A n) :
    pullbackTwo (mulBy O (G.A n) (p ^ n)) t = algebraMap O _
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n))
        (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul a b =>
    have h : pullbackTwo (mulBy O (G.A n) (p ^ n)) (a ⊗ₜ[O] b) =
        mulBy O (G.A n) (p ^ n) a ⊗ₜ[O] mulBy O (G.A n) (p ^ n) b := rfl
    rw [h, G.mulBy_pow_self, G.mulBy_pow_self, Algebra.TensorProduct.lift_tmul,
      Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, Algebra.TensorProduct.one_def]

theorem Chart.ev_nmul_pow : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, c.ev n (subst (nmul c.μ (p ^ n)) f) = algebraMap O _ (constantCoeff f)) ∧ (∀ s, c.ev₂ n (pull2 (nmul c.μ (p ^ n)) s) = algebraMap O _ (constantCoeff s)) ∧ ∀ f, c.ev (n + 1) (subst (nmul c.μ p) f) = G.mulP n (c.ev n f) := by
  intro p O _ _ G d c n
  refine ⟨fun f => ?_, fun s => ?_, fun f => ?_⟩
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.1, G.mulBy_pow_self,
      ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c n (p ^ n)).2.2, pullTwo_mulBy_pow_self,
      (GlobalTheory.T.ev_res_counit_compat p O G d c n).2]
  · rw [(GlobalTheory.T.formalChart_natMultiple_eval_properties p O G d c (n + 1) p).2.1, ← ((GlobalTheory.T.ev_res_counit_compat p O G d c n).1 f).1, mulP_res]

end GlobalTheory.QLog
