import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess leviV)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace Weight

variable {A B : LB X}

theorem SemiPosReg.tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf)
    (hψ' : ψ.SemiPosReg D) (hφ' : φ.SemiPosReg D) : (ψ.tens φ).SemiPosReg D := fun i c y hy ξ => by
  have h1 := (mem_ptsIn_inf.1 hy.2).1
  have h2 := (mem_ptsIn_inf.1 hy.2).2
  have e := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add (hψ.contDiffAt c hy.1 h1)
    (hφ.contDiffAt c hy.1 h2) ξ
  have := add_nonneg (hψ' i.1 c y ⟨hy.1, h1⟩ ξ) (hφ' i.2 c y ⟨hy.1, h2⟩ ξ)
  rw [← Complex.add_re, ← e] at this
  exact this

theorem SemiPosReg.of_mul {E : LB X} (ψ : Weight p σ E) {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hφ' : φ.SemiPosReg D) (c : ℝ) (hc : 0 ≤ c) (j : E.ι → B.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (B.U (j i)))
    (he : ∀ i y, ψ.φ i y = c * φ.φ (j i) y) : ψ.SemiPosReg D := fun i c' y hy ξ => by
  have h1 := hj i y hy.2
  have hf : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =
      fun v => ((c * φ.φ (j i) (c'.e.symm v) : ℝ) : ℂ) := funext fun v => by rw [he]
  rw [hf, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul c (hφ.contDiffAt c' hy.1 h1) ξ,
    Complex.re_ofReal_mul]
  exact mul_nonneg hc (hφ' (j i) c' y ⟨hy.1, h1⟩ ξ)

end Weight

namespace HermLB

variable {L M : HermLB p}

theorem SemiPos.tens (hL : L.SemiPos D) (hM : M.SemiPos D) : (L.tens M).SemiPos D := fun σ =>
  Weight.SemiPosReg.tens (L.cInf σ) (M.cInf σ) (hL σ) (hM σ)

theorem SemiPos.pow (hL : L.SemiPos D) (m : ℕ) : (L.pow m).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
    (fun _ _ h => mem_pow_iff.1 h) fun j y => (L.φ σ).zpow_φ (m : ℤ) j y

theorem semiPos_dual_pow_zero (hL : L.SemiPos D) : ((L.pow 0).dual).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) 0 le_rfl (fun j => j PUnit.unit)
    (fun _ _ h => (mem_pow_iff (n := ((0 : ℕ) : ℤ))).1 h) fun j y =>
      (congrArg (fun t : ℝ => -t) ((L.φ σ).zpow_φ ((0 : ℕ) : ℤ) j y)).trans (by simp)

end HermLB

namespace ArInt

variable {ι : Type} [Fintype ι]

theorem semiPos_zp {L : HermLB p} (hL : L.SemiPos D) {n : ℤ} (hn : 0 ≤ n) : (zp L n).SemiPos D := by
  have h0 : (-n).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
  unfold zp
  rw [h0]
  exact (hL.pow _).tens (HermLB.semiPos_dual_pow_zero hL)

theorem semiPos_comb (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (D : ℕ)
    (hL : ∀ i, (L i).SemiPos D) (hn : ∀ i, 0 ≤ n i) : (comb L n).SemiPos D := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => exact (HermLB.isNef_triv p D).semiPos
  | cons i l ih => exact (semiPos_zp (hL i) (hn i)).tens ih

example : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (ι : Type) [Fintype ι]
    (L : ι → GlobalTheory.HermLB p) (n : ι → ℤ) (D : ℕ), (∀ i, (L i).SemiPos D) → (∀ i, 0 ≤ n i) →
    (GlobalTheory.ArInt.comb L n).SemiPos D := @semiPos_comb

end ArInt

end GlobalTheory
