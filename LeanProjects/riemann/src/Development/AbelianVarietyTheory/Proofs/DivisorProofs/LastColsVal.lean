import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk

noncomputable section

open ValuativeRel
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unitMinorSet (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | (∀ i j, Y i j ∈ 𝒪[k]) ∧ ∃ f : Fin n ↪ Fin d, valuation k (Y.submatrix id f).det = 1}

def lastCols (n d : ℕ) (h : n ≤ d) : Fin n ↪ Fin d :=
  ⟨fun i => ⟨d - n + i, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩

theorem lastCols_val (n d : ℕ) (h : n ≤ d) (i : Fin n) : (lastCols n d h i : ℕ) = d - n + i := rfl

example (n d : ℕ) (h : n ≤ d) : GlobalTheory.FullRankCoinv.Y0 k n d ∈ unitMinorSet k n d := by
  refine ⟨fun i j => ?_, ⟨lastCols n d h, ?_⟩⟩
  · simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]; split_ifs <;> simp
  · have : (GlobalTheory.FullRankCoinv.Y0 k n d).submatrix id (lastCols n d h) = 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, id, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply, Matrix.one_apply]
      split_ifs with h1 h2 h2
      all_goals first | rfl | (exfalso; simp only [lastCols_val, Fin.ext_iff] at *; omega)
    rw [this]; simp

section
open MeasureTheory GlobalTheory.SplitFlip

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k}

theorem smallF_lact [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (h : GL (Fin n) k)
    (Φ : Matrix (Fin n) (Fin d) k → ℂ) (Y : Matrix (Fin n) (Fin d) k) :
    smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (GlobalTheory.FullRankCoinv.lact ν h Φ) Y =
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
  unfold smallF GlobalTheory.FullRankCoinv.lact
  have hI := integral_mul_left_eq_self (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (fun g : GL (Fin n) k => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
    (invT h)⁻¹
  rw [← hI]
  congr 1; funext g
  have e1 : gdet ((invT h)⁻¹ * g) = gdet h * gdet g := by
    rw [gdet_mul, show gdet (invT h)⁻¹ = (gdet (invT h))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
  simp only [e1, Units.val_mul, invT_inv_val, map_mul, apow_mul, Matrix.mul_assoc, Fintype.card_fin]
  ring

end

end GlobalTheory.FullRankCoinv.UnitMinor
