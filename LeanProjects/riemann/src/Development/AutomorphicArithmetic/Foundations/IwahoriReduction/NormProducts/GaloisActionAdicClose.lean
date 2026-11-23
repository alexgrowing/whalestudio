import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem UpperTheory.Kd.K4.galoisAction_adic_close {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) :
    ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → ∀ u,
      (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  induction hb using Submodule.span_induction with
  | mem b hb => exact GalCont.galB_sub_mem_of_Pol X l w b hb.1 n
  | zero => exact ⟨∅, fun s _ u => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs u => ?_⟩
    have h := Submodule.add_mem _ (hE s (fun x hx => hs x (Finset.mem_union_left _ hx)) u)
      (hF s (fun x hx => hs x (Finset.mem_union_right _ hx)) u)
    have e : (X.galB l s (a + b) - (a + b)) u =
        (X.galB l s a - a) u + (X.galB l s b - b) u := by
      simp only [map_add, Pi.add_apply, Pi.sub_apply]
      abel
    rw [e]
    exact h
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs u => ?_⟩
    have h := Submodule.smul_mem _ r (hE s hs u)
    have e : (X.galB l s (r • a) - r • a) u = r • (X.galB l s a - a) u := by
      simp only [map_smul, Pi.smul_apply, Pi.sub_apply, smul_sub]
    rw [e]
    exact h

theorem UpperTheory.Kd.K4.galc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), ∀ b ∈ X.B N l w, ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → CgF X l n (X.galB l s b) b := by
  intro Ω _ _ _ ε X l _ N w b hb n
  obtain ⟨E, hE⟩ := UpperTheory.Kd.K4.galoisAction_adic_close X l N w b hb n
  refine ⟨E, fun s hs u => ?_⟩
  have h := hE s hs u
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker] at h
  exact h
