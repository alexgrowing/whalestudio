import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad

theorem w_mul_exp_cmp_iff : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  intro F _ _ v ε _ k gn hgn b
  have hpr : (resP v).Prime := Fact.out
  have hio := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have hlog := log_w_eq (resP v) ε (ioOf (resP v) ε) hio
  have hwp : ε.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have h1 : ((resP v : ℕ) : AlgebraicClosure F) =
        algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [h1, ε.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hwp0 : 0 < ε.w ((resP v : ℕ) : AlgebraicClosure F) :=
    ε.w.pos (Nat.cast_ne_zero.2 hpr.ne_zero)
  have hlp : 0 < Real.log ((resP v : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hpr.one_lt)
  set c := -Real.log (ε.w ((resP v : ℕ) : AlgebraicClosure F)) / Real.log ((resP v : ℕ) : ℝ) with hc
  have hc0 : 0 < c := div_pos (neg_pos.2 (Real.log_neg hwp0 hwp)) hlp
  have hwb : ε.w b = ‖ioOf (resP v) ε b‖ ^ c := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp [Real.zero_rpow hc0.ne']
    · have hb' : 0 < ‖ioOf (resP v) ε b‖ := norm_pos_iff.2 ((map_ne_zero _).2 hb)
      rw [← Real.exp_log (ε.w.pos hb), hlog b, Real.rpow_def_of_pos hb', mul_comm]
  have hν : 0 < ∏ l, gn l := Finset.prod_pos fun l _ => hgn l
  have hexp : Real.exp (-∑ l, c * Real.log (gn l)) = (∏ l, gn l) ^ (-c) := by
    rw [Real.rpow_def_of_pos hν, ← Finset.mul_sum, Real.log_prod (fun l _ => (hgn l).ne')]
    ring_nf
  have hkey : ε.w b * Real.exp (-∑ l, c * Real.log (gn l)) = (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c := by
    rw [hexp, hwb, Real.div_rpow (norm_nonneg _) hν.le, Real.rpow_neg hν.le, div_eq_mul_inv]
  rw [hkey]
  have hx : 0 ≤ ‖ioOf (resP v) ε b‖ / ∏ l, gn l := div_nonneg (norm_nonneg _) hν.le
  have hle : (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff hx zero_le_one hc0, div_le_one hν]
  have hge : 1 ≤ (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ↔ ∏ l, gn l ≤ ‖ioOf (resP v) ε b‖ := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff zero_le_one hx hc0, one_le_div hν]
  refine ⟨hle, ?_, ?_⟩
  · rw [le_antisymm_iff, hle, hge, ← le_antisymm_iff]
  · rw [← Real.one_rpow c, Real.rpow_lt_rpow_iff hx zero_le_one hc0, div_lt_one hν]

end GlobalTheory.ShFam.Pad
