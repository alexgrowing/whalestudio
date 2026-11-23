import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ResidualModel

theorem of_discreteSpectrumGL (H : GlobalTheory.Published.DiscreteSpectrumGL) : GlobalTheory.Published.DiscreteSpectrumResidual := by
  intro E _ _ _ N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e w => ⟨(h5 V hV a d π hn e).exLoc w, (h5 V hV a d π hn e).loc w⟩⟩

theorem discreteSpectrumGL_iff : GlobalTheory.Published.DiscreteSpectrumGL ↔ GlobalTheory.Published.DiscreteSpectrumResidual ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
      ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a), IsNormalised π → IsSpehOf V π d →
        ∀ τ, ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m) := by
  refine ⟨fun H => ⟨of_discreteSpectrumGL H, fun E _ _ _ N hN V hV a d π hn e =>
    ((H E N hN).2.2.2.2 V hV a d π hn e).inf⟩, fun ⟨H, H'⟩ E _ _ _ N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e => ⟨fun w => (h5 V hV a d π hn e w).1, fun w => (h5 V hV a d π hn e w).2,
    H' E N hN V hV a d π hn e⟩⟩

theorem residual_one (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = 1 → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E 1), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E 1), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.DiscSpec.Model.discreteSpectrum_one (E := E)
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e w => ⟨(h5 V hV a d π hn e).exLoc w, (h5 V hV a d π hn e).loc w⟩⟩

theorem degrees_pos {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (h : IsSpehOf V π d) : 1 ≤ a ∧ 1 ≤ d := by
  have := h.mul_eq
  constructor
  · rcases a with _ | a
    · simp at this; omega
    · omega
  · rcases d with _ | d
    · simp at this; omega
    · omega

theorem isDiscrete_of_isNormalised (H : GlobalTheory.Published.DiscreteSpectrumResidual) {E : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (hn : IsNormalised π) :
    ∃ V : Submodule ℂ (Sm E a), IsDiscrete V ∧ IsSpehOf V π 1 :=
  ((H E a ha).2.1 a 1 π (one_mul a) hn).exists

end GlobalTheory.DiscSpec.ResidualModel

end
