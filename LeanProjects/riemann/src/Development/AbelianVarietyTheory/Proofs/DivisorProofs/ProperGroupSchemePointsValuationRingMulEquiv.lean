import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValPts

theorem points_generic_mulEquiv : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsProper G.hom → ∀ u : Sp U ⟶ S, ∃ e : (Over.mk u ⟶ G) ≃* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), ∀ P, (e P).left = spMap (algebraMap U Ω) ≫ P.left := by
  intro U Ω _ _ _ _ _ _ S G _ hp u
  let V : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) :=
    MonoidHom.mk' (V ≫ ·) fun x y => MonObj.comp_mul V x y
  have hv : ValuativeCriterion G.hom := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  have hb : Function.Bijective φ := by
    constructor
    · intro a b e
      have e' : spMap (algebraMap U Ω) ≫ a.left = spMap (algebraMap U Ω) ≫ b.left :=
        congrArg (fun q => q.left) e
      let Q : ValuativeCommSq G.hom :=
        { R := U, K := Ω, i₁ := spMap (algebraMap U Ω) ≫ a.left, i₂ := u,
          commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w a))⟩ }
      obtain ⟨W⟩ := hv Q
      have h1 := W.uniq ⟨a.left, rfl, Over.w a⟩
      have h2 := W.uniq ⟨b.left, e'.symm, Over.w b⟩
      exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l (h1.trans h2.symm))
    · intro y
      let Q : ValuativeCommSq G.hom :=
        { R := U, K := Ω, i₁ := y.left, i₂ := u, commSq := ⟨Over.w y⟩ }
      obtain ⟨W⟩ := hv Q
      exact ⟨Over.homMk W.default.l W.default.fac_right, Over.OverMorphism.ext W.default.fac_left⟩
  exact ⟨MulEquiv.ofBijective φ hb, fun P => rfl⟩

end GlobalTheory.ValPts
