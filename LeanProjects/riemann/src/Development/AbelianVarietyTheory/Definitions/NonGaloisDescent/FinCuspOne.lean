import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne

noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.DZero

def radS (F : Type) [Field F] {n : ℕ} (S : Finset (Fin n)) : Subgroup (GL (Fin n) F) :=
  GlobalTheory.FiniteGL.unipRadical F fun i => if i ∈ S then 0 else 1

def FinCusp {F : Type} [Field F] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin n) F) W) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∀ w : W, (∀ u ∈ radS F S, τ u w = w) → w = 0

def IsReg (q n : ℕ) (c : ZMod (q ^ n - 1)) : Prop :=
  ∀ i : ℕ, 0 < i → i < n → c * (q : ZMod (q ^ n - 1)) ^ i ≠ c

def Conj (q n : ℕ) (c d : ZMod (q ^ n - 1)) : Prop := ∃ i : ℕ, c * (q : ZMod (q ^ n - 1)) ^ i = d

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def CuspOn (π : Representation ℂ (GL (Fin n) k) V) (U : Submodule ℂ V) : Prop :=
  U ≤ fixed π (KOne k (Fin n)) ∧ (∀ κ ∈ KO k (Fin n), ∀ v ∈ U, π κ v ∈ U) ∧
    ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∀ v ∈ U, ∃ T : Finset (GL (Fin n) k), T.Nonempty ∧
      (∀ u ∈ T, u ∈ KO k (Fin n) ∧ u ∈ radS k S) ∧ ∑ u ∈ T, π u v = 0

def HasType {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) V)
    (τ : Representation ℂ (GL (Fin n) 𝓀[k]) W) (j : W →ₗ[ℂ] V) : Prop :=
  Function.Injective j ∧ ∀ (κ : GL (Fin n) 𝒪[k]) (w : W),
    π (GeneralLinearGroup.map (algebraMap 𝒪[k] k) κ) (j w) =
      j (τ (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) κ) w)

theorem cuspOn_bot (π : Representation ℂ (GL (Fin n) k) V) : CuspOn π ⊥ := by
  refine ⟨bot_le, fun κ _ v hv => ?_, fun S _ _ v hv => ⟨{1}, by simp, fun u hu => ?_, ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  · rw [Finset.mem_singleton] at hu; subst hu; exact ⟨one_mem _, one_mem _⟩
  · rw [Submodule.mem_bot] at hv; simp [hv]

theorem finCusp_one {F : Type} [Field F] {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin 1) F) W) : FinCusp τ := by
  rintro S ⟨i, hi⟩ hS
  exact absurd (Finset.eq_univ_iff_forall.2 fun j => Subsingleton.elim i j ▸ hi) hS

end GlobalTheory.DZero

end
