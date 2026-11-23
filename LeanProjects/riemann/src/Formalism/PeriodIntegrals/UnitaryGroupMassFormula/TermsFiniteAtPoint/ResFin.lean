import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ndS (D : D7) : ℕ :=
  (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))) ^ D.R.rS

def FInt : Prop :=
  ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (f : Fin D.R.rS → (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ a b, (VS D).hT (f a) (f b) = 0) → (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) →
    (∀ x ∈ L, ∀ a, (VS D).hT (F0.e a) x = 0 ∧ (VS D).hT (f a) x = 0) →
    Λ = latSpan (aaS D) F0.e ⊔ L ⊔ latSpan (fun a => (aaS D a)⁻¹) f →
    0 < ndS D ∧ ∀ x ∈ Λ, ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (ndS D : D.host.E) * (VS D).hT (f c) x

def ResFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V), Λ.FG → ∀ c : ℕ, 0 < c →
      ∃ (R : Type) (_ : Finite R) (ρ : V → R), ∀ x ∈ Λ, ∀ y ∈ Λ, ρ x = ρ y →
        ∃ l ∈ Λ, y - x = (c : E) • l

end PI.TermsAtPtFiniteW
