import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_mono (n : ℕ) {s₁ s₂ : kˣ} (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    polyBall n s₁ ≤ polyBall n s₂ :=
  fun x hx i => show valuation k (x.toAdd i) ≤ valuation k (s₂ : k) from
    le_trans (show valuation k (x.toAdd i) ≤ valuation k (s₁ : k) from hx i) h

theorem exists_mem_polyBall {n : ℕ} (x : Multiplicative (Fin n → k)) :
    ∃ s : kˣ, x ∈ polyBall n s := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin n => valuation k (x.toAdd i))
  obtain ⟨y, hy⟩ := valuation_surjective (max M 1)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy.symm ▸ le_max_right M 1 : (1 : ValueGroupWithZero k) ≤ 0) (by simp)
  refine ⟨Units.mk0 y hy0, fun i => ?_⟩
  show valuation k (x.toAdd i) ≤ valuation k y
  rw [hy]
  exact le_trans (hM i) (le_max_left _ _)

theorem twKer_polyBall_mono (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨⟨x, hx⟩, v, rfl⟩
  exact Submodule.subset_span ⟨⟨x, polyBall_mono n h hx⟩, v, rfl⟩

theorem exists_mem_twKer_polyBall (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) (v : V)
    (hv : v ∈ twKer ρ ⊤ (resChr ψ a ⊤)) :
    ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, -⟩, u, rfl⟩ := hw
    obtain ⟨s, hs⟩ := exists_mem_polyBall x
    exact ⟨s, Submodule.subset_span ⟨⟨x, hs⟩, u, rfl⟩⟩
  | zero => exact ⟨1, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, h₁⟩ := hx
    obtain ⟨s₂, h₂⟩ := hy
    rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
    · exact ⟨s₂, Submodule.add_mem _ (twKer_polyBall_mono ψ ρ a h h₁) h₂⟩
    · exact ⟨s₁, Submodule.add_mem _ h₁ (twKer_polyBall_mono ψ ρ a h h₂)⟩
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, Submodule.smul_mem _ c hs⟩

end GlobalTheory.CompanionTheory.MirFourier
