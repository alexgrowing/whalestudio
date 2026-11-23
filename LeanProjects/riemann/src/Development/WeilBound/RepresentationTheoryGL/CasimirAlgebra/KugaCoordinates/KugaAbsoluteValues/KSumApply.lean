import Mathlib

noncomputable section

open Fin Function

namespace PositivityTheory.Rg.Cz

section
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

def kLop (T : P →ₗ[ℝ] Module.End ℂ M) : P →ₗ[ℝ] M →ₗ[ℝ] M where
  toFun X := (T X).restrictScalars ℝ
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp

def kPre (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P →ₗ[ℝ] P [⋀^Fin m]→ₗ[ℝ] M where
  toFun X := (kLop T X).compAlternatingMap η
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp

def kD (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P [⋀^Fin (m + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin (kPre T η)

theorem kD_apply (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (v : Fin (m + 1) → P) :
    kD T η v = ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • T (v i) (η (i.removeNth v)) := by
  simp [kD, AlternatingMap.alternatizeUncurryFin_apply, kPre, kLop]

theorem kSum_apply {N : Type} [AddCommGroup N] [Module ℝ N] {ι β : Type} (s : Finset β)
    (F : β → P [⋀^ι]→ₗ[ℝ] N) (v : ι → P) : (∑ i ∈ s, F i) v = ∑ i ∈ s, F i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

def kDel (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) : P [⋀^Fin n]→ₗ[ℝ] M :=
  ∑ i, (kLop T (b i)).compAlternatingMap (θ.curryLeft (b i))

theorem kDel_apply (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (v : Fin n → P) :
    kDel T b θ v = ∑ i, T (b i) (θ (Matrix.vecCons (b i) v)) := by
  unfold kDel
  rw [kSum_apply]
  rfl

def kIp (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) {β : Type} [Fintype β] (b : β → P) {m : ℕ}
    (η θ : P [⋀^Fin m]→ₗ[ℝ] M) : ℂ :=
  ∑ I : Fin m → β, B (η (b ∘ I)) (θ (b ∘ I))

end

end PositivityTheory.Rg.Cz

end
