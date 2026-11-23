import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.ModelFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel Filter Topology
open GlobalTheory.LocMod GlobalTheory.LocMod.Witness GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatFBCompare

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem val_lt_one_iff (x : K) : valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ (not_lt.1 hx)
  exact absurd hn (not_lt.2 h2)

end Val

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]

theorem ι_one (p : Place D k) : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]

theorem π_e (p : Place D k) : p.π p.e = 1 := by rw [← ι_one, p.π_ι]

def compare {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (p : Place D k) (p' : Place D k') (h : p'.e = p.e) : k →+* k' where
  toFun x := p'.π (p.ι x)
  map_one' := by rw [ι_one, ← h, π_e]
  map_mul' x y := by rw [ι_mul, RingHom.map_mul]
  map_zero' := by rw [map_zero, RingHom.map_zero]
  map_add' x y := by rw [map_add, RingHom.map_add]

variable {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  [Fintype Z'] [DecidableEq Z'] {S T : HSp D}

section Scal

variable {K : Type} [Field K] {γ t : Kˣ} {s : K} {σ : ℕ}

end Scal

section Frames

variable {q : GlobalTheory.FinPl.SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {σ : ℕ}
  {γ t : kˣ} {s : k} (hγ : (γ : k) = (Place.ofSplitPt q).xi) (ht : (t : k) = s * γ ^ (σ + 1))
include hγ ht

end Frames

section Local

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def dg (n : Type) [DecidableEq n] (c : ℕ) (r : kˣ) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  diagonal (Sum.elim (fun _ => 1) fun i => (r : k) ^ i.val)

variable [MeasurableSpace k] [BorelSpace k] {c : ℕ}

end Local

theorem ι_xi (p : Place D k) (x : k) : p.ι (p.xi * x) = incA D D.host.xi0 * p.ι x := by
  rw [ι_mul]
  change p.ι (p.π _) * _ = _
  rw [p.ι_π, mul_comm p.e, mul_assoc, e_ι]

section Change

variable {q : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {σ : ℕ} {γ γ' t : kˣ}

end Change

def ren (n : Type) [DecidableEq n] (A B : Type) (a : k) : Matrix (n ⊕ A) (n ⊕ B) k :=
  fromBlocks 1 0 0 (Matrix.of fun _ _ => a)

section Rename₂

variable {n m A B : Type} [Fintype n] [DecidableEq n] [Unique A] [Unique B] (a : k)

end Rename₂

end GlobalTheory.FlatFBCompare
end
