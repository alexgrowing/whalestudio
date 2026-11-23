import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem conj_LvTw_div_dLoc_inert : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  intro D B m v w hv hq hB hm hs
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hqV : qV D.host.F v = q := rfl
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have hstar : ((star (m w) : ℂˣ) : ℂ) = (-1) ^ D.R.nV := by
    rw [Units.coe_star, hm]; simp
  have hinv : ((m w : ℂ))⁻¹ = (-1) ^ D.R.nV := by rw [hm, ← inv_pow, inv_neg, inv_one]
  have hnp : npow v (-(2 * ((1 + (D.R.t : ℂ)) / 2))) = ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by
    rw [npow, show -(2 * ((1 + (D.R.t : ℂ)) / 2)) = -((D.R.t + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  rw [LvTw_inert B m hv hq, hnp, hinv, hstar, hqV, map_div₀, Complex.conj_ofReal]
  have hx : starRingEnd ℂ ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) =
      (-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by simp
  have hconjE : starRingEnd ℂ (eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹)) =
      eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) := by
    conv_rhs => rw [← hB]
    simp only [eulerFac, eulerPoly, map_inv₀, map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, map_sub, map_one, map_mul, Units.coe_star, hx]
    rfl
  rw [hconjE, div_eq_mul_inv]
  congr 1
  have hqt : ∀ i : ℕ, quadTerm D v i = (-1 : ℝ) ^ i / (q : ℝ) ^ i := by
    intro i; rw [quadTerm, hs]
  have hd : ((dLoc D v : ℝ) : ℂ)⁻¹ = ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - (-1 : ℂ) ^ i / (q : ℂ) ^ i) := by
    rw [dLoc, Complex.ofReal_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by rfl) fun i _ => ?_
    rw [Complex.ofReal_inv, inv_inv, hqt]
    push_cast; ring
  rw [hd]
  have key : ∀ a j : ℕ, (-1 : ℂ) ^ a / (q : ℂ) ^ a = (-(q : ℂ)) ^ j * ((-1 : ℂ) ^ (a + j) * ((q : ℂ) ^ (a + j))⁻¹) := by
    intro a j
    calc (-1 : ℂ) ^ a / (q : ℂ) ^ a = ((-1 : ℂ) ^ j * (-1) ^ j) * ((-1 : ℂ) ^ a / (q : ℂ) ^ a) * ((q : ℂ) ^ j * ((q : ℂ) ^ j)⁻¹) := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow, mul_inv_cancel₀ (pow_ne_zero _ hq0)]; ring
      _ = _ := by rw [neg_pow, pow_add, pow_add, mul_inv]; ring
  refine Finset.prod_nbij' (fun i => D.R.r + D.R.t - i) (fun j => D.R.r + D.R.t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_Ioc] at hi; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ioc]; omega
  · intro i hi; rw [Finset.mem_Ioc] at hi; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro i hi
    have hi' := Finset.mem_Ioc.1 hi
    have e : D.R.nV = i + (D.R.r + D.R.t - i) := by show D.R.r + D.R.t = _; omega
    rw [e, key i (D.R.r + D.R.t - i), ← e]
    show _ = 1 - _ * (_ * ((q : ℂ) ^ (D.R.r + D.R.t))⁻¹)
    rfl

end GlobalTheory.FinZeta
