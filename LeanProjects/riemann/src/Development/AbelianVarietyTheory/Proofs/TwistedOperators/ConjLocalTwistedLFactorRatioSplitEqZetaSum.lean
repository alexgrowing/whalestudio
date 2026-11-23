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

namespace GlobalTheory.LocZetaSplit

theorem prod_map_conj_eq (A : Multiset ℂˣ) (hA : A.map star = A.map (·⁻¹)) (f : ℂ → ℂ) :
    (A.map fun b : ℂˣ => f (starRingEnd ℂ (b : ℂ))).prod = (A.map fun b : ℂ ˣ => f ((b : ℂ)⁻¹)).prod := by
  have h := congrArg (fun M : Multiset ℂˣ => (M.map fun b : ℂˣ => f (b : ℂ)).prod) hA
  simpa [Multiset.map_map, Function.comp_def, Units.coe_star, Units.val_inv_eq_inv_val] using h

theorem conj_LvTw_div_dLoc : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → (B w).map star = (B w).map (·⁻¹) → m w * m w' = 1 → ‖(m w : ℂ)‖ = 1 → quadSign D v = 1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) := by
  intro D B m v w w' hne hv hqw hqw' hB' hstar hm1 hnorm hsign
  classical
  set s : ℂ := (1 + (D.R.t : ℂ)) / 2 with hs
  set X : ℂ := npow w (-s) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX : starRingEnd ℂ X = X := by
    have : X = (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((1 + (D.R.t : ℝ)) / 2)) : ℝ) := by
      rw [hXdef, npow, Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl
    rw [this, Complex.conj_ofReal]
  have hX' : npow w' (-s) = X := by rw [hXdef, npow, npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have hμc : starRingEnd ℂ μ = μ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hμc' : starRingEnd ℂ μ⁻¹ = μ := by rw [map_inv₀, hμc, inv_inv]
  have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v s = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hc1 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z * μ * X)⁻¹)
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc', hX]
    exact this
  have hc2 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z⁻¹ * μ⁻¹ * X)⁻¹)
    simp only [inv_inv] at this
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc, hX]
    exact this
  have hstarμ : ((star (m w) : ℂˣ) : ℂ) = μ⁻¹ := by rw [Units.coe_star, ← hμc]; rfl
  have hr1 : eulerFac ((B w).map (star (m w) * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, hstarμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, hstarμ, mul_inv, inv_inv]
    ring
  have hd : (dLoc D v : ℂ) = (∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dLoc]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [quadTerm, hsign, qV, hqw]
  rw [map_div₀, Complex.conj_ofReal, hd, div_inv_eq_mul, hL, map_mul, hc1, hc2, hr1, hr2]
  ring

end GlobalTheory.LocZetaSplit
