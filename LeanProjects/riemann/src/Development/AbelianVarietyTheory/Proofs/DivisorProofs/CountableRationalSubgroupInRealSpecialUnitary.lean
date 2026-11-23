import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem countable_inReal_of_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  intro E _ _ _ r Ψ G Γ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Units.val_injective.countable
  have h : ((Γ.map (embGL Ψ r) : Subgroup (Ψ → GL (Fin r) ℂ)) : Set (Ψ → GL (Fin r) ℂ)).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  haveI : Countable (Γ.map (embGL Ψ r)) := h.to_subtype
  refine Function.Injective.countable
    (f := fun x : inReal Ψ G Γ => (⟨x.1.1, x.2⟩ : Γ.map (embGL Ψ r))) ?_
  intro x y hxy
  have h2 : x.1.1 = y.1.1 := Subtype.mk.inj hxy
  exact Subtype.ext (Subtype.ext h2)

end GlobalTheory.CovTop.VolUp
