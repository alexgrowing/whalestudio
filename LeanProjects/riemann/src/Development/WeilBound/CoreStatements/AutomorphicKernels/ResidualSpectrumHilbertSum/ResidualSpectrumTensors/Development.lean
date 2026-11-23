import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumHilbertSum

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)

def Clause1 : Prop :=
  ∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
      IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
    ∀ (μ : Measure (GA E N)) [μ.IsHaarMeasure] (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      classes V μ ≤ (classes (⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a)
        (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) μ).topologicalClosure

def Clause2 : Prop :=
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ∀ (a d : ℕ) (π : CuspSub E a),
    π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V'

def Clause3 : Prop :=
  ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
    π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

def Core : Prop :=
  ∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → 2 ≤ d → π.IsUnitary → IsNormalised π →
      IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
    ∀ (μ : Measure (GA E N)) [μ.IsHaarMeasure] (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      classes V μ ≤ (classes ((⨆ (π : CuspSub E N) (_ : π.IsUnitary ∧ IsNormalised π), π.V) ⊔
        ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a)
          (_ : d * a = N ∧ 2 ≤ d ∧ π.IsUnitary ∧ IsNormalised π), J a π d) μ).topologicalClosure

def CuspDiscrete : Prop :=
  ∀ π : CuspSub E N, π.IsUnitary → IsNormalised π → IsDiscrete π.V

end PositivityTheory.RSHS

end
