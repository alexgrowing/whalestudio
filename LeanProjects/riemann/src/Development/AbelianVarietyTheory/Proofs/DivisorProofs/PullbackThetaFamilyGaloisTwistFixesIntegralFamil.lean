import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem famTw_eq_of_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  intro R _ _ I D N σ F₀ s hs
  have hL := D.P.isLB
  refine fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (sec_ext' hL fun y J hJ => ?_)
  show sval (termPull D (Kb R) (TwF σ) N α (s.s α)) (𝟙 _) y J = _
  refine (sval_pullOver _ _ _ _ hJ).trans ?_
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, ← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ]
  congr 1
  have e : (famMap D (Kb R) (TwF σ)).left ≫ (DegPre.prB D (Kb R)).left = (DegPre.prB D (TwF σ)).left :=
    congrArg (fun q => q.left) (famMap_snd D (Kb R) (TwF σ))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => 𝟙 _ ≫ q) e)

end GlobalTheory.Mum.Conj
