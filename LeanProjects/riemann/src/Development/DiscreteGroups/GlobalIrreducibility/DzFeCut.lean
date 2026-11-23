import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix

namespace DiscreteGroups.sglob.DzFe

theorem cycM_mul_tr (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨l, rfl⟩ := (finRotate n).surjective i
  rw [Finset.sum_eq_single l]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
  · intro b _ hb
    have : ¬ finRotate n l = finRotate n b := fun h => hb ((finRotate n).injective h).symm
    rw [Matrix.of_apply, Matrix.of_apply, if_neg this, zero_mul]
  · simp

theorem tr_mul_cycM (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (finRotate n i)]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h ((finRotate n).injective e))]
  · intro b _ hb
    rw [Matrix.of_apply, Matrix.of_apply, if_neg (Ne.symm hb), zero_mul]
  · simp

def cyc (g n : ℕ) : GL (Fin n) (ZMod g) :=
  ⟨Matrix.of fun i k => if i = finRotate n k then 1 else 0, Matrix.of fun i k => if finRotate n i = k then 1 else 0,
    cycM_mul_tr g n, tr_mul_cycM g n⟩

def IsColFix {g n : ℕ} (j : ℕ) (h : GL (Fin n) (ZMod g)) : Prop :=
  (∀ i k : Fin n, (k : ℕ) ≠ 0 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = if i = k then 1 else 0) ∧
    ∀ i k : Fin n, (k : ℕ) = 0 → j < (i : ℕ) → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = 0

def IsRowFix {g n : ℕ} (j : ℕ) (h : GL (Fin n) (ZMod g)) : Prop :=
  (∀ i k : Fin n, (i : ℕ) ≠ 0 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = if i = k then 1 else 0) ∧
    ∀ i k : Fin n, (i : ℕ) = 0 → 0 < (k : ℕ) → (k : ℕ) ≤ j + 1 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = 0

def FunctionalEquationAtIndex : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (m : ℕ) (ψ₀ : AddChar (ZMod g) Circle), ψ₀ ≠ 1 →
    ∀ τ : FDRep ℂ (Gn g (m + 1)), IsCusp τ.character → ∀ γ : ℂ,
    (∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v) →
    ∀ l : Module.Dual ℂ τ, IsFunctional ψ₀ τ.ρ l →
    ∀ j : ℕ, j < m → ∀ v : τ, (∀ h, IsColFix j h → τ.ρ h v = v) → (∀ h, IsRowFix j h → τ.ρ h v = v) →
      γ * l v = (g : ℂ) ^ ((m + 1) * m / 2 + m - j) * l (τ.ρ (cyc g (m + 1))⁻¹ v)

end DiscreteGroups.sglob.DzFe
