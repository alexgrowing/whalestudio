import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.NormalCore
open GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ebox {A D : Type} (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ r i j : kˣ) : k)}

theorem box_eq_ebox {A D : Type} (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    GlobalTheory.RankCoinv.box ϖ C e = ebox ϖ C (fun i _ => e i) := rfl

theorem ebox_eq_of_mem {A D : Type} {ϖ : kˣ} {C X : Matrix A D k} {r : A → D → ℕ} (hX : X ∈ ebox ϖ C r) :
    ebox ϖ X r = ebox ϖ C r := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)

open Classical in

def pv {n d : ℕ} (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)) : ℂ :=
  if h : B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d ∧
      B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d then
    Bf ⟨_, h.1⟩ ⟨_, h.2⟩
  else 0

theorem pv_eq {n d : ℕ} (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) {B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)}
    (Ψ₁ Ψ₂ : fullRk k n d) (h₁ : Ψ₁.1 = B₁.indicator 1) (h₂ : Ψ₂.1 = B₂.indicator 1) : pv Bf B₁ B₂ = Bf Ψ₁ Ψ₂ := by
  have m₁ : B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := h₁ ▸ Ψ₁.2
  have m₂ : B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := h₂ ▸ Ψ₂.2
  rw [pv, dif_pos ⟨m₁, m₂⟩]
  congr 1
  · exact congrArg Bf (Subtype.ext h₁.symm)
  · exact Subtype.ext h₂.symm

def baseCellRadiiAtEntry {n d : ℕ} (i₀ : Fin n) (j₀ : Fin d) (N : ℕ) : Fin n → Fin d → ℕ :=
  fun i j => if j = j₀ ∧ i ≠ i₀ then N + 1 else N

def baseCellRadiiAtColumn {n d : ℕ} (j₀ : Fin d) (N : ℕ) : Fin n → Fin d → ℕ :=
  fun _ j => if j = j₀ then N + 1 else N

def scaledBoxRadiiAtEntry {n d : ℕ} (i₀ : Fin n) (j₀ : Fin d) (N : ℕ) : Fin n → Fin d → ℕ :=
  fun i j => if i = i₀ ∧ j ≠ j₀ then N - 1 else if j = j₀ ∧ i ≠ i₀ then N + 1 else N

def dgl {m : ℕ} (i₀ : Fin m) (t : kˣ) : GL (Fin m) k where
  val := diagonal (Function.update (1 : Fin m → k) i₀ (t : k))
  inv := diagonal (Function.update (1 : Fin m → k) i₀ ((t⁻¹ : kˣ) : k))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i
    by_cases h : i = i₀ <;> simp [h, Function.update_apply]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i
    by_cases h : i = i₀ <;> simp [h, Function.update_apply]

theorem dgl_val {m : ℕ} (i₀ : Fin m) (t : kˣ) :
    (dgl i₀ t).1 = diagonal (Function.update (1 : Fin m → k) i₀ (t : k)) := rfl

theorem gdet_dgl {m : ℕ} (i₀ : Fin m) (t : kˣ) : gdet (dgl i₀ t) = t := by
  ext
  simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply, dgl_val, det_diagonal]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  rw [Finset.prod_eq_one (fun i hi => by simp [Function.update_apply, (Finset.ne_of_mem_erase hi)])]
  simp

end GlobalTheory.NormalCore
