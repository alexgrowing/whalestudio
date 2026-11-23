import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePointsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem surj_of_finite_dimS {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] (g : ℕ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = g)
    (hY : ∀ y : Y, IsClosed ({y} : Set Y) → ringKrullDim (Y.presheaf.stalk y) = g)
    (o : X) (ho : IsClosed ({o} : Set X)) : Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  suffices hη : genericPoint Y ∈ Set.range f by
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      closure_minimal (Set.singleton_subset_iff.mpr hη) hcl
    have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
    rw [hc] at hsub
    exact hsub (Set.mem_univ y)
  by_contra hη
  have hmono : StrictMono f := GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite f
  let F : WithTop X → Y := fun a => WithTop.recTopCoe (genericPoint Y) (fun x => f x) a
  have hF : StrictMono F := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top =>
        refine lt_of_le_of_ne (genericPoint_specializes (f a)) ?_
        intro h
        have hi : Inseparable (f a) (genericPoint Y) := h.symm
        exact hη ⟨a, hi.eq⟩
      | coe b => exact hmono (WithTop.coe_lt_coe.mp hab)
  have h1 := Order.coheight_le_coheight_apply_of_strictMono F hF (o : WithTop X)
  rw [Order.coheight_coe_withTop] at h1
  have hfo : IsClosed ({f o} : Set Y) := by
    have := f.isClosedMap _ ho
    rwa [Set.image_singleton] at this
  have e1 := hX o ho
  have e2 := hY (f o) hfo
  rw [ringKrullDim_stalk_eq_coheight] at e1 e2
  have e1' : Order.coheight o = g := by exact_mod_cast e1
  have e2' : Order.coheight (f o) = g := by exact_mod_cast e2
  change Order.coheight o + 1 ≤ Order.coheight (f o) at h1
  rw [e1', e2'] at h1
  exact absurd h1 (by norm_cast; omega)

theorem isClosed_originS {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] [IsProper G.hom] :
    IsClosed ({η[G].left (IsLocalRing.closedPoint Ω)} : Set G.left) := by
  have hc : IsClosed ({IsLocalRing.closedPoint Ω} : Set (Sp Ω)) := isClosed_singleton
  have h1 := (η[G].left).isClosedEmbedding.isClosedMap _ hc
  convert h1 using 1
  exact (Set.image_singleton).symm

theorem flat_surj_of_finite {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (g : ℕ) (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (f : G ⟶ G') [IsMonHom f] (hf : IsFinite f.left) :
    Flat f.left ∧ Surjective f.left := by
  haveI := hG.smooth
  haveI := hG'.smooth
  haveI := hG.proper
  haveI := hG'.proper
  haveI := hf
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G hG
  haveI : AlgebraicGeometry.IsIntegral G'.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G' hG'
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hsurj : Surjective f.left :=
    surj_of_finite_dimS f.left g
      (fun x hx => GlobalTheory.CutDegree.ringKrullDim_stalk hgG hx)
      (fun y hy => GlobalTheory.CutDegree.ringKrullDim_stalk hgG' hy)
      _ (isClosed_originS (G := G))
  haveI := hsurj
  exact ⟨GlobalTheory.SS.flat_of_isDominant_grpHom Ω G G' f, hsurj⟩

end PositivityTheory.PrwZar.Z2
