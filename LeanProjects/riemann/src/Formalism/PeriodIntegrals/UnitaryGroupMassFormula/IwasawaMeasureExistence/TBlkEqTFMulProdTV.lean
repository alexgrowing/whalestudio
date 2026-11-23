import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviHaarMeasureExists

noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory Topology Set NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables PI.IwaMeasEx.AfT

section Factors

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

open Classical in

def tF (m : I.GA) (i : Fin c.length) : ℝ :=
  if h : IsUnit (Fr.blkF c m i).det then Formalism.L2.S.S7.GLOne.nrmF I h.unit else 0

def tV (m : I.GA) (v : InfinitePlace I.F) (i : Fin c.length) : ℝ := ‖(Fr.blkV c m v i).det‖ ^ 2

def dF (m : I.GA) : ℝ := cn_dens c.blocksFun (I.n - 2 * J) I.f (chv (PI.IwaMeasEx.eExp I c) (tF Fr c m))

def dV (m : I.GA) (v : InfinitePlace I.F) : ℝ :=
  cn_dens c.blocksFun (I.n - 2 * J) I.f (chv (PI.IwaMeasEx.eExp I c) (tV Fr c m v))

end Factors

section Local

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

def uniF : Subgroup I.Gf := (uniGL Fr.colF (levW c)).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def uniV (v : InfinitePlace I.F) : Subgroup (Formalism.REAL.UJ (I.ε v)) :=
  (uniGL (Fr.colV v) (levW c)).comap (Formalism.REAL.UJ (I.ε v)).subtype

structure PNF (μ : Measure I.Gf) : Prop where
  sfin : SigmaFinite μ
  ne : μ ≠ 0
  supp : μ (uniF Fr c : Set I.Gf)ᶜ = 0
  cpt : ∀ s : Set I.Gf, IsCompact s → μ s ≠ ⊤
  inv : ∀ n ∈ uniF Fr c, μ.map (fun x => n * x) = μ

structure PNV (v : InfinitePlace I.F) (μ : Measure (Formalism.REAL.UJ (I.ε v))) : Prop where
  sfin : SigmaFinite μ
  ne : μ ≠ 0
  supp : μ (uniV Fr c v : Set (Formalism.REAL.UJ (I.ε v)))ᶜ = 0
  cpt : ∀ s : Set (Formalism.REAL.UJ (I.ε v)), IsCompact s → μ s ≠ ⊤
  inv : ∀ n ∈ uniV Fr c v, μ.map (fun x => n * x) = μ

end Local

def ModF : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), PI.IwaMeasEx.Sk.Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    ∀ m ∈ D.toWittFrame.leviA c, ∃ μ : Measure X.I.Gf, PNF D.toWittFrame c μ ∧
      μ.map (fun x => m.2 * x * m.2⁻¹) = ENNReal.ofReal (dF D.toWittFrame c m) • μ

def ModV : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), PI.IwaMeasEx.Sk.Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    ∀ (v : InfinitePlace X.I.F), ∀ m ∈ D.toWittFrame.leviA c, ∃ μ : Measure (Formalism.REAL.UJ (X.I.ε v)),
      PNV D.toWittFrame c v μ ∧ μ.map (fun x => m.1 v * x * (m.1 v)⁻¹) = ENNReal.ofReal (dV D.toWittFrame c m v) • μ

end PI.IwaMeasEx.LP

end
