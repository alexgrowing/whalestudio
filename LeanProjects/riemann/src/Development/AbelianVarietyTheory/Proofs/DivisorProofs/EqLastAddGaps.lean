import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CompHS
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

def headWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ (i : ℕ) ≤ k then 1 else 0

open Classical in

def tailWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ k < (i : ℕ) then -1 else 0

open Classical in

def unitWt (τ : Psi H) (a : ℤ) : AllWt.Weight Dw := fun τ' _ => if τ' = τ then a else 0

theorem eq_last_add_gaps {N : ℕ} (v : Fin N → ℤ) (hN : 0 < N) (i : Fin N) :
    v i = v ⟨N - 1, by omega⟩ + ∑ k ∈ Finset.range (N - 1), if (i : ℕ) ≤ k then gap v k else 0 := by
  have h := ofGaps_gap v ⟨N - 1, by omega⟩ i
  simp only [ofGaps] at h
  have hi : (i : ℕ) ≤ N - 1 := by omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have e : (Finset.range (N - 1)).filter (fun k => (i : ℕ) ≤ k) = Finset.Ico (i : ℕ) (N - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sub _ hi]
  linarith

open Classical in

def piece (Dw : Datum H) (τ : Psi H) (k : ℕ) : AllWt.Weight Dw :=
  if k + 1 < Dw.p + Dw.q then (if k < Dw.p then headWt τ k else tailWt τ k) else 0

open Classical in
theorem piece_apply (τ τ' : Psi H) (k : ℕ) (i : Fin (Dw.p + Dw.q)) : piece Dw τ k τ' i =
    if τ' = τ then (if k + 1 < Dw.p + Dw.q then (if k < Dw.p then (if (i : ℕ) ≤ k then 1 else 0)
      else (if k < (i : ℕ) then -1 else 0)) else 0) else 0 := by
  unfold piece headWt tailWt
  by_cases h : τ' = τ <;> split_ifs <;> simp_all

open Classical in
theorem unitWt_apply (τ τ' : Psi H) (a : ℤ) (i : Fin (Dw.p + Dw.q)) :
    unitWt τ a τ' i = if τ' = τ then a else 0 := rfl

open Classical in
theorem decomp (la : AllWt.Weight Dw) (hla : GapGe 0 la) (hN : 0 < Dw.p + Dw.q) :
    let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
    la = ∑ x ∈ (Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum (Finset.univ : Finset (Psi H × Bool)),
      (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
        (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat) x) •
      (Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
        (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1)) x) := by
  intro cτ
  classical
  funext τ' i
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_disjSum, Finset.sum_product, Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, piece_apply, unitWt_apply, Fintype.sum_bool,
    mul_ite, mul_zero, if_true, if_false]
  rw [Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, nsmul_eq_mul, Bool.false_eq_true, if_false, mul_one]
  have hv := eq_last_add_gaps (la τ') hN i
  have hterm : ∀ y ∈ Finset.range (Dw.p + Dw.q - 1), (if (i : ℕ) ≤ y then gap (la τ') y else 0) =
      ((gap (la τ') y).toNat : ℤ) * (if y + 1 < Dw.p + Dw.q then (if y < Dw.p then (if (i : ℕ) ≤ y then 1 else 0)
        else (if y < (i : ℕ) then -1 else 0)) else 0) + (if Dw.p ≤ y then gap (la τ') y else 0) := by
    intro y hy
    have hy' : y + 1 < Dw.p + Dw.q := by simp only [Finset.mem_range] at hy; omega
    have hg : 0 ≤ gap (la τ') y := hla τ' y hy'
    rw [Int.toNat_of_nonneg hg, if_pos hy']
    split_ifs <;> first | omega | simp <;> omega
  have hc := Int.toNat_sub_toNat_neg (cτ τ')
  have hcdef : cτ τ' = la τ' ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ') k else 0 := rfl
  rw [hv, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  linarith

end GlobalTheory.NefWt
