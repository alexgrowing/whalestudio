import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

variable {L n}

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def SatAtS (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ) : Prop :=
  ∃ f ∈ S, f ≠ 0 ∧ ∃ U : Subgroup (GAf L n), (∀ κ ∈ U, rt L n κ f = f) ∧
    (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧
    ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV L⁺ v) h α • f

theorem satAt_iff (π : AutRep L n) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (α : Fin (n / 2) → ℂ) : SatAt π Dv α ↔ SatAtS π.S Dv α := Iff.rfl

end Formalism.L2.NG
