import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KMapInto

section
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}

theorem comap_bot_or_top (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (W : Submodule ℂ H) (hW : IsKStableOn ε σ W) :
    (∀ s : S, T s ∈ W → s = 0) ∨ (∀ s : S, T s ∈ W) := by
  obtain ⟨_, hSst, hSirr, _, _⟩ := hS
  have hle : (W.comap T).map S.subtype ≤ S := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hst : IsKStableOn ε σ ((W.comap T).map S.subtype) := by
    rintro g hg _ ⟨s, hs, rfl⟩
    refine ⟨⟨σ g s, hSst g hg s s.2⟩, ?_, rfl⟩
    show T _ ∈ W
    rw [hT g hg s _ rfl]
    exact hW g hg _ hs
  rcases hSirr _ hle hst with h | h
  · left
    intro s hs
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := ⟨s, hs, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · right
    intro s
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := by
      rw [h]
      exact s.2
    obtain ⟨t, ht, hts⟩ := hmem
    obtain rfl : t = s := Subtype.ext hts
    exact ht

theorem inj_or_zero (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)) :
    (∀ s : S, T s = 0 → s = 0) ∨ (∀ s : S, T s = 0) := by
  have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
    intro g _ v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  simpa only [Submodule.mem_bot] using comap_bot_or_top hS T hT ⊥ hbot

theorem range_isKType (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hinj : ∀ s : S, T s = 0 → s = 0) : IsKTypeOf ε σ Λ (LinearMap.range T) := by
  have hS' := hS
  obtain ⟨hfin, hSst, _, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS'
  have key : ∀ s : S, ∀ t ∈ Kset ε, ∀ c : ℂ, σ t (T s) = c • T s → σ t s = c • (s : H) := by
    intro s t ht c h
    have h2 : T (⟨σ t s, hSst t ht s s.2⟩ - c • s) = 0 := by
      rw [map_sub, map_smul, hT t ht s _ rfl, h, sub_self]
    exact congrArg Subtype.val (sub_eq_zero.mp (hinj _ h2))
  refine ⟨inferInstance, ?_, ?_, ⟨T ⟨v, hvS⟩, ⟨⟨v, hvS⟩, rfl⟩, ?_, ?_⟩, ?_⟩
  · rintro g hg _ ⟨s, rfl⟩
    exact ⟨⟨σ g s, hSst g hg s s.2⟩, hT g hg s _ rfl⟩
  · intro S' hle hst
    rcases comap_bot_or_top hS T hT S' hst with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨s, rfl⟩ := hle hx
      rw [h s hx, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨s, rfl⟩
      exact h s
  · intro h
    exact hv0 (congrArg Subtype.val (hinj _ h))
  · intro θ hθ
    rw [← hT _ hθ ⟨v, hvS⟩ ⟨_, hSst _ hθ v hvS⟩ rfl, ← map_smul]
    exact congrArg T (Subtype.ext (hvw θ hθ))
  · intro μ w hw hw0 hww
    obtain ⟨s, rfl⟩ := hw
    refine hdom μ s s.2 ?_ ?_
    · intro h
      apply hw0
      obtain rfl : s = 0 := Subtype.ext h
      exact map_zero T
    · intro θ hθ
      exact key s _ hθ _ (hww θ hθ)

theorem scalar_of_range_le (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hle : ∀ s, T s ∈ S) : ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  have hS' := hS
  obtain ⟨hfin, _, _, ⟨v, hvS, hv0, _⟩, _⟩ := hS'
  haveI : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.codRestrict S T hle)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hK : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s →
      (T - c • S.subtype) s' = σ k ((T - c • S.subtype) s) := by
    intro k hk s s' hs'
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, map_sub, map_smul,
      hT k hk s s' hs', hs']
  rcases inj_or_zero hS (T - c • S.subtype) hK with h | h
  · exfalso
    have e : T w = c • (w : H) := congrArg Subtype.val hw.apply_eq_smul
    refine hw.2 (h w ?_)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, e, sub_self]
  · intro s
    have hs := h s
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, sub_eq_zero] at hs
    exact hs

end

theorem kMap_lowKSub_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  intro n ε lam H _ _ _ σ _ hK T hT
  rcases inj_or_zero hK T hT with h | h
  · refine scalar_of_range_le hK T hT ?_
    intro s
    have hle : LinearMap.range T ≤ lowKSub ε lam σ := le_sSup (range_isKType hK T hT h)
    exact hle ⟨s, rfl⟩
  · exact ⟨0, fun s => by rw [h s, zero_smul]⟩

end GlobalTheory.KMapInto
