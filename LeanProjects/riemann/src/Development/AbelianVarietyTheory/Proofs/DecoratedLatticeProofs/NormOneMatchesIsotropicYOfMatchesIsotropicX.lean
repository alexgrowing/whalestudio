import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

open GlobalTheory.IwaPlace in

theorem hermAt_colMul_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D)
    (x : Fin S.rank → AE D) : hermAt S (colMul d.jY i a) x = a * cA D ((d.pX *ᵥ x) i) := by
  have hg : ∀ j k, cA D (gA S j k) = gA S k j := fun j k => congrFun (congrFun (adj_gA S) k) j
  rw [d.pX_eq]
  simp only [hermAt, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, adj, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, cA_cA, hg, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pX_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (b : AE D) :
    (d.pX *ᵥ colMul d.jX i b) i = b := by
  have h := congrFun (congrFun d.pX_jX i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mulVec, dotProduct, colMul]
  calc ∑ k, d.pX i k * (b * d.jX k i) = b * ∑ k, d.pX i k * d.jX k i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = b := by rw [h, mul_one]

theorem mem_idAt_of_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ) {b : AE D} (hb : colMul d.jX i b ∈ latV S L (· = v)) : b ∈ idAt D (· = v) := by
  rw [← pX_colMul_jX d i b]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).1 _ hb) i

theorem colMul_jY_mem_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {M : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (hL : IsSelfDualC S L) (hM : MonoAt d L M v) (i : Fin ρ) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    colMul d.jY i a ∈ latV S L (· = v) ↔
      ∀ b, colMul d.jX i b ∈ latV S L (· = v) → a * cA D b ∈ intAt D (· = v) := by
  have hy : ∀ k, colMul d.jY i a k ∈ idAt D (· = v) := fun k => Ideal.mul_mem_right _ _ ha
  rw [(GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).2.2 _ hy]
  constructor
  · intro h b hb
    have h1 := h _ hb
    rwa [hermAt_colMul_jY, pX_colMul_jX] at h1
  · intro h x hx
    rw [hermAt_colMul_jY]
    exact h _ (((hM x).1 hx).1 i)

theorem dualLine_match : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  intro D S S₀ ρ d L L' M M' v c hL hL' hM hM' hc hX i a ha
  have hca : c * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
  rw [colMul_jY_mem_iff d hL hM i ha, colMul_jY_mem_iff d hL' hM' i hca]
  have hcc : c * cA D c = 1 := hc.1
  constructor
  · intro h b' hb'
    have hbI : cA D c * b' ∈ idAt D (· = v) :=
      Ideal.mul_mem_left _ _ (mem_idAt_of_colMul_jX d hL' v i hb')
    have e : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
    have h1 : colMul d.jX i (cA D c * b') ∈ latV S L (· = v) := (hX i _ hbI).2 (by rw [e]; exact hb')
    have h2 := h _ h1
    rw [map_mul, cA_cA] at h2
    have e2 : c * a * cA D b' = a * (c * cA D b') := by ring
    rw [e2]
    exact h2
  · intro h b hb
    have h1 := (hX i b (mem_idAt_of_colMul_jX d hL v i hb)).1 hb
    have h2 := h _ h1
    have e : c * a * cA D (c * b) = a * cA D b := by
      rw [map_mul]
      calc c * a * (cA D c * cA D b) = (c * cA D c) * (a * cA D b) := by ring
        _ = a * cA D b := by rw [hcc, one_mul]
    rwa [e] at h2

end GlobalTheory.Core.Mi.LatMatch

end
