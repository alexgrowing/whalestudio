import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ResidualSpectrumByClass : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
        V ≤ ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a) (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
