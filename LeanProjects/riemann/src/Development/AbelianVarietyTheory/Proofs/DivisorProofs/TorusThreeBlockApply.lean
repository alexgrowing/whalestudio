import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent

namespace GlobalTheory.IndJacBlock

def sz3 (d : ℕ) (j : Fin 3) : ℕ := if (j : ℕ) = 1 then d - 2 else 1

theorem three_block_size_sum {d : ℕ} (h : 2 ≤ d) : ∑ j, sz3 d j = d := by
  simp [Fin.sum_univ_three, sz3]; omega

def place3 {d : ℕ} (h : 2 ≤ d) : (Σ j : Fin 3, Fin (sz3 d j)) ≃ Fin d := stdBlocks (sz3 d) (three_block_size_sum h)

def b2 (n d : ℕ) (j : Fin 2) : ℕ := if (j : ℕ) = 0 then d - n else n

theorem block_size_pair_sum {n d : ℕ} (h : n ≤ d) : b2 n d 0 + b2 n d 1 = d := by
  simp [b2]; omega

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def torEntry (d : ℕ) (p : kˣ × kˣ) (j : Fin 3) : kˣ := if (j : ℕ) = 0 then p.1 else if (j : ℕ) = 2 then p.2 else 1

def tor3 (d : ℕ) : kˣ × kˣ →* Levi k (fun j : Fin 3 => Fin (sz3 d j)) where
  toFun p j := Matrix.GeneralLinearGroup.scalar _ (torEntry k d p j)
  map_one' := by funext j; simp [torEntry]
  map_mul' p q := by
    funext j
    simp only [Pi.mul_apply, ← map_mul]
    congr 1
    simp only [torEntry, Prod.fst_mul, Prod.snd_mul]
    split_ifs <;> simp

theorem torus_three_block_apply (d : ℕ) (p : kˣ × kˣ) (j : Fin 3) :
    tor3 k d p j = Matrix.GeneralLinearGroup.scalar _ (torEntry k d p j) := rfl

def chi2 (ν : kˣ →* ℂˣ) (j : Fin 2) : kˣ →* ℂˣ := if (j : ℕ) = 0 then 1 else ν⁻¹

def cellChar₂ (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (i j : Fin 2) (p : kˣ × kˣ) : ℂ :=
  ((χ i p.1 * absPow k ((1 - (b i : ℂ)) / 2) p.1 * χ j p.2 * absPow k (((b j : ℂ) - 1) / 2) p.2 : ℂˣ) : ℂ)

end GlobalTheory.IndJacBlock
