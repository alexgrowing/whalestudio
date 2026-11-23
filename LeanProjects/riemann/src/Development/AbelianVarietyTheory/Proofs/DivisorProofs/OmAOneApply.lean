import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det

def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _

variable (k) in

def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}

def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))

open Classical in

def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k :=
  if h : ∃ J, IsFirstMax Y J then GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1 else 1

theorem tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

theorem tw_ne_zero (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem omA_one_apply (ν β : kˣ →* ℂˣ) {a b : ℕ} (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (Y : Matrix (Fin a) (Fin (a + b)) k) : omA ν β g 1 Ψ Y = (tw ν (a + b) g)⁻¹ * Ψ ((g⁻¹).val * Y) := by
  have e : apow (gdet g) (-(((a + b : ℕ)) : ℂ) / 2) = (apow (gdet g) (((a + b : ℕ) : ℂ) / 2))⁻¹ := by
    rw [neg_div, apow_neg]
  simp only [omA, tw, Fintype.card_fin, e, map_one, Units.val_one, apow_one, mul_one, invT_val, inv_one,
    transpose_one, Units.val_inv_eq_inv_val, mul_inv, Matrix.mul_one]

theorem minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by
  rw [minor, minor, ← det_mul]
  congr 1

end GlobalTheory.RankFibreKer
