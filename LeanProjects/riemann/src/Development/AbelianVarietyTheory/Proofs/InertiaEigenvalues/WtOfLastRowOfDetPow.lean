import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

def yInf (g : GA E (m + 1)) : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i)

def yFin (g : GA E (m + 1)) : Fin (m + 1) → Af E := fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)

def sqrtC (Φ : (Fin (m + 1) → Cinf E) → ℂ) (u : Fin (m + 1) → Cinf E) : ℂ := (Real.sqrt (Φ u).re : ℂ)

def fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) : ℂ :=
  φ (g * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g)

def wt (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℝ≥0 := Real.toNNReal ((indN N (yFin g)).re * detPow E (m + 1) x g)

theorem yInf_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yInf g' = yInf g := by
  funext i; exact congrArg (fun r => pInf E (r i)) h

theorem yFin_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yFin g' = yFin g := by
  funext i; exact congrArg (fun r => GlobalTheory.RSJ.pFin E (r i)) h

theorem fT_of_lastRow {φ : GA E (m + 1) → ℂ} {Φ : (Fin (m + 1) → Cinf E) → ℂ} {g g' : GA E (m + 1)}
    (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) :
    fT φ Φ g' = φ (g' * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g) := by
  rw [fT, yInf_of_lastRow h]

theorem wt_of_lastRow_of_detPow {N : ℕ} {x : ℝ} {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g)
    (hd : detPow E (m + 1) x g' = detPow E (m + 1) x g) : wt N x g' = wt N x g := by
  rw [wt, wt, yFin_of_lastRow h, hd]

end GlobalTheory.ZUnf
