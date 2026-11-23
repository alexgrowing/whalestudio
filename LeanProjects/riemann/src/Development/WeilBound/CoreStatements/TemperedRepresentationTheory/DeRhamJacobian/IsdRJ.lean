import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal

namespace PositivityTheory.HodgeLocalCharacter.HLC

def toGL1 (R : Type) [CommRing R] : Rˣ →* GL (Fin 1) R :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

def IsdRJ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)
    (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ) : Prop :=
  Bw.IsdRE P LL' ((toGL1 ↥LL'.1).comp ψ) ∧
    ∀ τ' a, Bw.multE P LL' ((toGL1 ↥LL'.1).comp ψ) τ' a = if a = J τ' then 1 else 0

end PositivityTheory.HodgeLocalCharacter.HLC
