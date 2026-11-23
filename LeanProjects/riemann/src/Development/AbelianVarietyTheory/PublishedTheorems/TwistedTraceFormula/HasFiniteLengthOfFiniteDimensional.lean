import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.FinitenessModel

theorem padic (h : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (p : ℕ) [Fact p.Prime] :
    IrreducibleAdmissible ℚ_[p] :=
  haveI := GlobalTheory.SplitWeil.Model.padic_localField p
  (h ℚ_[p]).1

theorem admissible_of_subsingleton {G V : Type} [Group G] [TopologicalSpace G] [Subsingleton G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hs : IsSmooth π)
    (h : π.IsIrreducible) : IsAdmissible π := by
  haveI : IsSimpleOrder (Subrepresentation π) := h
  have hfin : FiniteDimensional ℂ V := by
    by_cases hV : ∃ v : V, v ≠ 0
    · obtain ⟨v, hv⟩ := hV
      let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by
        rw [Subsingleton.elim g 1, map_one]; exact hw⟩
      rcases eq_bot_or_eq_top S with hS | hS
      · have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
        rw [hS] at this
        exact absurd this hv
      · have h2 : Submodule.span ℂ {v} = ⊤ := congrArg Subrepresentation.toSubmodule hS
        exact ⟨h2 ▸ Submodule.fg_span_singleton v⟩
    · push Not at hV
      haveI : Subsingleton V := ⟨fun a b => by rw [hV a, hV b]⟩
      infer_instance
  exact ⟨hs, fun _ _ _ => inferInstance⟩

theorem hasFiniteLength_of_finiteDimensional {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ G V) : HasFiniteLength π := by
  let φ : Subrepresentation π ↪o Submodule ℂ V :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  exact (hasFiniteLength_iff_wellFounded π).2 ⟨φ.wellFoundedGT, φ.wellFoundedLT⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem hasFiniteLength_jac (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ (GL n k) V) : HasFiniteLength (jac e π) :=
  hasFiniteLength_of_finiteDimensional _

theorem not_hasFiniteLength_trivial :
    IsSmooth (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) ∧
      ¬ HasFiniteLength (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) := by
  refine ⟨fun v => by simp, fun h => ?_⟩
  have h1 := ((hasFiniteLength_iff_wellFounded _).1 h).1
  let φ : Submodule ℂ (ℕ →₀ ℂ) ↪o Subrepresentation (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) :=
    ⟨⟨fun S => ⟨S, fun g v hv => by simpa using hv⟩,
      fun a b hab => congrArg Subrepresentation.toSubmodule hab⟩, Iff.rfl⟩
  haveI : IsNoetherian ℂ (ℕ →₀ ℂ) := isNoetherian_iff'.2 φ.wellFoundedGT
  exact Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℂ) (ι := ℕ))
    inferInstance

end GlobalTheory.SmGL.FinitenessModel
