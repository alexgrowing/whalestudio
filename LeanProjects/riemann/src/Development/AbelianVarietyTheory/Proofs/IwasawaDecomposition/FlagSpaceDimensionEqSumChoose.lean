import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.FlagDimSum

theorem mul_add_choose_two (p q : ℕ) :
    p * q + p.choose 2 + q.choose 2 = (p + q).choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1).choose 2 = q + q.choose 2 := by
      rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right]
    have h2 : (p + q + 1).choose 2 = (p + q) + (p + q).choose 2 := by
      rw [Nat.choose_succ_succ' (p + q) 1, Nat.choose_one_right]
    rw [← add_assoc, h1, h2, ← ih]
    ring

theorem dim_add_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      Module.finrank ℚ E / 2 := by
    omega
  have hs : ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
    simp_rw [Datum.mult, apply_ite (fun n : ℕ => n.choose 2)]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h2, smul_eq_mul, smul_eq_mul, mul_add]
  rw [hs, Datum.dim, ← Nat.choose_two_right, ← mul_add_choose_two, mul_assoc, ← mul_add, ← add_assoc]

end GlobalTheory.FlagDimSum
