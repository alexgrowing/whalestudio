import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockA

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def eBq (j : ℕ) : {x // x ∈ blkB (n := n) j} ≃ {x // ¬ x ∈ blkA (n := n) j} :=
  Equiv.subtypeEquivRight (fun x => mem_blkB j x)

def piP (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) : Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr σA ((eBq j).permCongr τ)

def resA (j : ℕ) (σ : Equiv.Perm (Fin n)) (h : ∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) :
    Equiv.Perm (blkA (n := n) j) :=
  σ.subtypePerm fun r => (h r).symm

def resB (j : ℕ) (σ : Equiv.Perm (Fin n)) (h : ∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) :
    Equiv.Perm (blkB (n := n) j) :=
  (eBq j).symm.permCongr (σ.subtypePerm (p := fun x => ¬ x ∈ blkA (n := n) j) fun r => not_congr (h r).symm)

end PositivityTheory.Rg.Sw.LVs.TC
