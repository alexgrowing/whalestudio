import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SrcL (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) : Prop :=
  (∃ (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ) (A : ValuationSubring Ω)
      (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    ¬ l ∣ g.M ∧ ‖ι.symm (g.a l)‖ = 1 ∧ KillsMu l χ ∧
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) ∧ OverL l A ∧ IsFlagOn W (Dec (F := ℚ) A) κ ∧
    ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 1 s : Qbar l) * (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) * ((dt W (s : G ℚ Ω) : Qbar l)⁻¹ * (χ (s : G ℚ Ω) : Qbar l)) = 1) ∧
  ∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ →
    ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s

def VanishOrdL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : R2 Ω l, admitted ι e W → SrcL ι e W → BlochKatoSelmerVanishes l (Loc.colRep W)

end GlobalTheory.Ord2

end
