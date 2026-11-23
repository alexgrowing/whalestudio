import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.LiftMod

theorem kstable_of_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (U : Submodule ℂ V) (h : ∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ U, units act a b u ∈ U) : KStable act U := by
  intro X hX u hu
  have hXs : X = ∑ a, ∑ b, X a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hXs, map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun a _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun b _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hab : sameBlock a b
  · refine U.smul_mem _ (h a b ?_ u hu)
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (hab : False).elim
    · exact (hab : False).elim
    · rfl
  · rw [hX a b hab, zero_smul]; exact U.zero_mem

theorem lift_mod : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  intro p q V _ _ act hG N N' hN hN' μ v hv h1 h2
  obtain ⟨hLie, hwt, hloc⟩ := hG
  obtain ⟨U, hvU, hUfd, hUst, -⟩ := hloc {v}
  have hU : KStable act U := kstable_of_units act U hUst
  have hvU' : v ∈ U := hvU v (Finset.mem_singleton_self v)
  haveI : FiniteDimensional ℂ U := hUfd
  let W : Submodule ℂ V := N' ⊓ U
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ U)
  have sW : KStable act W := fun X hX w hw => ⟨hN' X hX w hw.1, hU X hX w hw.2⟩
  have hKL : Formalism.MainNotions.SchurIrreducible.IsKLieAct act := fun Y Z _ _ => hLie Y Z
  obtain ⟨T', hT'W, hTN, hhw⟩ := GlobalTheory.DegKeep.joint_lift (ι := Unit) (fun _ => act) (fun _ => hKL) (fun _ v => hwt v)
    (fun w w' hne => absurd (Subsingleton.elim w w') hne) W N (fun _ => sW) (fun _ => hN) (fun _ => μ) v ⟨hv, hvU'⟩
    (fun _ c => h1 c) (fun _ c d hcd => h2 c d hcd)
  exact ⟨T', hT'W.1, hhw (), hTN⟩

end GlobalTheory.HoweR.LiftMod
