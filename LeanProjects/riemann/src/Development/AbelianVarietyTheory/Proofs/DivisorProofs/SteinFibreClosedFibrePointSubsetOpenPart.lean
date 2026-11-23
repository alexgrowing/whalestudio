import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem steinFibre_subset_range : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  intro R _ _ _ hR M G' _ _ hG E H' X'' ν i P'' a'' b'' hν hi hcomm hab hb ha hconn hH0 z hz w hw
  haveI := hν; haveI := hb; haveI := ha; haveI := hi
  have hsep : IsSeparated (a'' ≫ b'') := inferInstance
  have hR' : IsNoetherianRing R := hR.1
  have hog : i ≫ a'' ≫ b'' = H'.ι ≫ E.f := by
    rw [hab, ← Category.assoc, hcomm, Category.assoc]
    exact congrArg (H'.ι ≫ ·) (pullback.lift_fst _ _ _)
  have hy : PSpace.str R E.N (b'' (a'' (i z))) = closedPoint R := by
    have h1 : i ≫ a'' ≫ b'' ≫ PSpace.str R E.N = H'.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
      rw [reassoc_of% hog, E.f_over]
    have h2 := congrArg (fun f => f.base z) h1
    simp only [Scheme.Hom.comp_base, ContinuousMap.comp_apply] at h2
    exact h2.trans hz
  obtain ⟨C, hC, hCeq⟩ := GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed R M.S M.π M.proper G' hG.smooth E H' X'' i (a'' ≫ b'') hsep hog hH0
    (b'' (a'' (i z))) hy
  have hfib : ∀ p : X'', a'' p = a'' (i z) → p ∈ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} := by
    intro p hp
    show b'' (a'' p) = b'' (a'' (i z))
    rw [hp]
  have key : ∀ p : X'', a'' p = a'' (i z) → p ∈ C → p ∈ Set.range i := fun p hp hpC =>
    (show p ∈ Set.range i ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq ▸ ⟨hpC, hfib p hp⟩).1
  by_contra hwi
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  obtain ⟨p, hpF, hpU, hpC⟩ := hconn (a'' (i z)) (Set.range i) Cᶜ hU hC.isOpen_compl
    (fun p hp => by
      by_cases h : p ∈ C
      · exact Or.inl (key p hp h)
      · exact Or.inr h)
    ⟨i z, rfl, z, rfl⟩ ⟨w, hw, fun h => hwi (key w hw h)⟩
  exact hpC (show p ∈ C ∩ (a'' ≫ b'') ⁻¹' {b'' (a'' (i z))} from hCeq.symm ▸ ⟨hpU, hfib p hpF⟩).1

end GlobalTheory.Mum
