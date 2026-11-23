import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSmallDict

def IsRootOne (ζ : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def IsAlgUnit (ζ : ℂ) : Prop :=
  ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1

variable {D : D7}

def IsStdLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i

def unitPt (S T : HSp D) (a : Formalism.L2.Theta.AE D) (o : ℕ) : WO S T := fun i j => if i.1 = o + j.1 then a else 0

def cosetFn {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T) : WO S T → ℂ := fun y =>
  if IsHalf a y ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - x i j)) then 1 else 0

def modul (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : Ideal (𝓞 D.host.E) :=
  ∏ w ∈ P, w.asIdeal ^ c w

def GoodIdem (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  IsIdemSum e P ∧ ∀ w ∈ P, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

theorem IsRootOne.one : IsRootOne 1 := ⟨1, one_pos, one_pow 1⟩

theorem IsRootOne.mul {a b : ℂ} (ha : IsRootOne a) (hb : IsRootOne b) : IsRootOne (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨n, hn, h'⟩ := hb
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, pow_mul, h, mul_comm m n, pow_mul, h', one_pow, one_pow, one_mul]⟩

theorem IsRootOne.ne_zero {a : ℂ} (ha : IsRootOne a) : a ≠ 0 := by
  obtain ⟨m, hm, h⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem IsRootOne.inv {a : ℂ} (ha : IsRootOne a) : IsRootOne a⁻¹ := by
  obtain ⟨m, hm, h⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩

theorem IsRootOne.isAlgUnit {a : ℂ} (ha : IsRootOne a) : IsAlgUnit a := by
  have h0 := ha.ne_zero
  obtain ⟨m, hm, h⟩ := ha
  have hq : a ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hm (by rw [h]; exact isAlgebraic_one))
  refine ⟨h0, hq, fun p _ lam => ?_⟩
  have h1 : (⟨a, hq⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have h2 : ‖lam ⟨a, hq⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  unfold lamC
  rw [dif_pos hq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2

theorem IsAlgUnit.mul {a b : ℂ} (ha : IsAlgUnit a) (hb : IsAlgUnit b) : IsAlgUnit (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, Qbar.mul_mem ha.2.1 hb.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam ha.2.1 hb.2.1, norm_mul, ha.2.2 p lam, hb.2.2 p lam, one_mul]⟩

end GlobalTheory.BotSmallDict

end
