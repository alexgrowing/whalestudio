import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.PhaseQuad

open GlobalTheory.RootEx

section General
variable {V k : Type*} [AddCommGroup V] [CommRing k] (O : Subring k) (S : Set V)

def Aff (f : V → k) : Prop := ∃ a : V → k, (∀ v l, f (v + l) = f v + a l) ∧ ∀ l ∈ S, a l ∈ O

def Quad (f : V → k) : Prop := ∀ v, ∀ l ∈ S, ∀ l' ∈ S, f (v + l + l') + f v - (f (v + l) + f (v + l')) ∈ O

variable {O S}

theorem Aff.const (c : k) : Aff O S fun _ => c := ⟨fun _ => 0, by simp, fun _ _ => zero_mem _⟩

theorem Aff.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Aff O S (f i)) :
    Aff O S fun v => ∑ i ∈ s, f i v := by
  choose a ha hO using h
  exact ⟨fun l => ∑ i ∈ s, a i l, fun v l => by simp only [ha, Finset.sum_add_distrib],
    fun l hl => sum_mem fun i _ => hO i l hl⟩

theorem Aff.ite (p : Prop) [Decidable p] {f : V → k} (h : Aff O S f) : Aff O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using Aff.const 0

theorem Aff.quad {f : V → k} (h : Aff O S f) : Quad O S f := by
  obtain ⟨a, ha, -⟩ := h
  intro v l _ l' _
  have : f (v + l + l') + f v - (f (v + l) + f (v + l')) = 0 := by
    rw [ha (v + l), ha v l']; ring
  rw [this]; exact zero_mem _

theorem Aff.mul {f g : V → k} (hf : Aff O S f) (hg : Aff O S g) : Quad O S fun v => f v * g v := by
  obtain ⟨a, ha, haO⟩ := hf
  obtain ⟨b, hb, hbO⟩ := hg
  intro v l hl l' hl'
  have : f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) =
      a l * b l' + a l' * b l := by
    rw [ha (v + l), ha v l', ha v l, hb (v + l), hb v l', hb v l]; ring
  show f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) ∈ O
  rw [this]
  exact add_mem (mul_mem (haO l hl) (hbO l' hl')) (mul_mem (haO l' hl') (hbO l hl))

theorem Quad.add {f g : V → k} (hf : Quad O S f) (hg : Quad O S g) : Quad O S fun v => f v + g v := by
  intro v l hl l' hl'
  convert add_mem (hf v l hl l' hl') (hg v l hl l' hl') using 1
  ring

theorem Quad.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Quad O S (f i)) :
    Quad O S fun v => ∑ i ∈ s, f i v := by
  intro v l hl l' hl'
  convert sum_mem (t := s) fun i _ => h i v l hl l' hl' using 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem Quad.ite (p : Prop) [Decidable p] {f : V → k} (h : Quad O S f) : Quad O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using (Aff.const 0).quad

end General

section Phase
variable {k : Type*} [Field k] {G : Grid k} (O : Subring k)

def intVars (G : Grid k) : Set (Vars G) := {e | ∀ j r, e j r ∈ O}

theorem aff_stepPt (j : Fin (G.m - 1)) (x₀ : Matrix (Fin (topRank G (j + 1))) (Fin (topRank G j)) k) (r s) :
    Aff O (intVars O G) fun e : Vars G => stepPt x₀ (e j) r s := by
  by_cases h : Free ((G.m - 2 - j) / 2 + 1) (r, s) ∨ Kept (r, s)
  · refine ⟨fun l => l j ⟨(r, s), h⟩, fun v l => ?_, fun l hl => hl j _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_pos h, Pi.add_apply, add_assoc]
  · refine ⟨fun _ => 0, fun v l => ?_, fun _ _ => zero_mem _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]

theorem aff_rowVar (x : ColArgs G) (j : ℕ) (s) : Aff O (intVars O G) fun e : Vars G => rowVar x e j s := by
  by_cases h : j < G.m - 1
  · simp only [rowVar, dif_pos h]
    exact Aff.sum _ fun l => Aff.ite _ (aff_stepPt O ⟨j, h⟩ (x j) _ _)
  · simp only [rowVar, dif_neg h]
    exact Aff.const _

theorem quad_phase (x : ColArgs G) : Quad O (intVars O G) fun e : Vars G => phase x e := by
  unfold phase
  refine Quad.sum _ fun j => Quad.add ?_ (Quad.ite _ (Quad.sum _ fun r => ?_))
  · exact (Aff.sum _ fun i => aff_stepPt O j (x j) _ _).quad
  · exact (aff_rowVar O x _ r).mul (aff_stepPt O j (x j) _ _)

end Phase

theorem psi_phase_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  intro k _ _ _ _ G ψ hψ ϖ hϖ n x v l l' hl hl'
  have hint : ∀ e ∈ varLat G ϖ n, e ∈ intVars 𝒪[k] G := fun e he j r => by
    have h1 : valuation k ((ϖ ^ n : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val]
      exact pow_mem hϖ.mem n
    exact (he j r).trans h1
  have hq := quad_phase 𝒪[k] x v l (hint l hl) l' (hint l' hl')
  have h1 : ψ (-(phase x (v + l + l') + phase x v - (phase x (v + l) + phase x (v + l')))) = 1 :=
    (hψ 1).2 le_rfl _ (by rw [Valuation.map_neg, map_one]; exact hq)
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← one_mul (ψ (-phase x (v + l) + -phase x (v + l'))), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  ring

end GlobalTheory.UnfoldLoss.PhaseQuad
