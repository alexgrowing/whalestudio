import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BotFormula

def toFinE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)).toRingEquiv.trans
    (GlobalTheory.LFun.finAdEquiv ℚ D.host.E)

def IsFinPt {D : D7} (WW : HSp D) (g : Formalism.L2.Theta.GA D WW) {n : ℕ} (h : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Prop :=
  g ∈ GfC WW ∧ ∃ e : WW.rank = n, ∀ i j,
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom WW g : GL (Fin WW.rank) _) : Matrix (Fin WW.rank) (Fin WW.rank) _) i j) =
      toFinE D (((h : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Fin.cast e i) (Fin.cast e j))

def minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n) : PolF D d₁ a₁ :=
  MvPolynomial.rename (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast hd k.2.1, Fin.cast ha k.2.2))
    (GlobalTheory.NormSum.minorPol D T)

theorem IsFinPt.cast {D : D7} {WW : HSp D} {g : Formalism.L2.Theta.GA D WW} {n n' : ℕ} (e : n' = n) {h : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    (hg : IsFinPt WW g h) : IsFinPt WW g (e ▸ h : Formalism.MainNotions.StandardLatticesGL3.GA D n') := by
  subst e; exact hg

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  unfold lamC
  rw [dif_pos (Qbar.mul_mem hx hy), dif_pos hx, dif_pos hy, ← map_mul]
  rfl

end GlobalTheory.BotFormula
