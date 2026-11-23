import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

def OneCStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ θ : Fam P.D.toPre F 1, NuGe P.D Q F v 1 θ 0 →
      (∃ (σ : P.D.toPre.SecB 1 0)
        (σF : LB.Sec (LB.LinComb P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1))),
        GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1) σF
          (P.D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB P.D.toPre F).left 1 ∧
        (∀ j, (θ.s 0).f j = σF.f j) ∧
        ¬ ∃ σ' : P.D.toPre.SecB 1 0, ∀ j, σ.f j = constFn P.D.toPre.P.A.hom _ ϖ * σ'.f j) →
    ∀ θα : Fam P.D.toPre F (1 * N), PullAl P.D F P.oD α 1 N θ θα →
    ∀ s : Fam P.D.toPre F (1 * N), NuGe P.D Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt P.D.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ P.A.A))
        (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b)
          (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam P.D.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, P.ToA F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam P.D.toPre F (1 * N),
          PhiRel P.D.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i

end ReciprocityTheory.ChartRestriction.G.H1
