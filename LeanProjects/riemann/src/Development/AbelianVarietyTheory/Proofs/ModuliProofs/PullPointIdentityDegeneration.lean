import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

theorem isPullGtF_self_of_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hD : IsPullDeg (RingHom.id R) D D), IsIdPull hD → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g : GtPtF D F), IsPullGtF (RingHom.id R) hD F g g := by
  intro R _ _ D hD ⟨hx, he, hw⟩ F _ _ g
  refine ⟨by rw [he, Category.comp_id], fun χ => ?_⟩
  have key : ∀ χ' : D.X, χ = χ' → ∃ hψ : ∀ k : Fin 4,
      DegPre.gtφ D F g.b χ k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
        𝟙 _ ≫ DegPre.gtφ D F g.b χ' k,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (g.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
        DegPre.gtε _ hψ (g.s χ')) := by
    rintro _ rfl
    have hψ : ∀ k : Fin 4,
      DegPre.gtφ D F g.b χ k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
        𝟙 _ ≫ DegPre.gtφ D F g.b χ k := fun k => by rw [he, Category.comp_id, Category.id_comp]
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ (𝟙 _) _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2
      (pmaps_self_of_tautological he hD.w hw _ _ _ (g.isGen _))⟩
  exact key _ (hx χ).symm

end GlobalTheory.TorsionFormCompare
