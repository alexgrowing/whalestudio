import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKReal GlobalTheory.AinfK

namespace GlobalTheory.FrobOrder

theorem iterate_of_pow {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (x : E) (l : ℕ)
    (h : σ x = x ^ l) (j : ℕ) : (⇑σ)^[j] x = x ^ l ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ']

theorem sigma_root {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) {m : ℕ} (h0 : 0 < m)
    (hm : ¬ l ∣ m) (hx : x ^ m = 1) : (P.PD K).σ x = x ^ l := by
  have hc : (x : Om l) ^ m = 1 := congrArg Subtype.val hx
  have h1 : (P.PD K).σ x ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : (((P.PD K).σ x : ↥(K0 K)) : Om l) ^ m = 1 := congrArg Subtype.val h1
  have h3 : ((x : Om l) ^ l) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]
  have h4 : ‖(x : Om l)‖ = 1 := GlobalTheory.Pst.norm_eq_one_of_pow_eq_one h0 hc
  have h5 := P.PD_σ K x h4.le
  have h6 := GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hm h2 h3 h5
  exact Subtype.ext h6

end GlobalTheory.FrobOrder
