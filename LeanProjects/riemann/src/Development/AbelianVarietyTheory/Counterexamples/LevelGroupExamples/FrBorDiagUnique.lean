import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameRelCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_diag_unique {S : Type} [CommRing S] [Algebra c.F S] (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S)
    (h : FrBor t y y') (h' : FrBor t' y y') : t = t' := by
  obtain ⟨x, xo, u, tn, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', tn', e', b', s', g'⟩ := y'
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := h
  obtain ⟨-, hu', pm', hs', hf', ha'⟩ := h'
  dsimp only at hx hu hu' pm pm' hs hf ha hs' hf' ha'
  subst hx
  have h1 : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · exact hf.trans (Category.id_comp _).symm
    · exact hs.trans (Category.id_comp _).symm
  have h2 : pm' = 𝟙 _ := by
    apply pullback.hom_ext
    · exact hf'.trans (Category.id_comp _).symm
    · exact hs'.trans (Category.id_comp _).symm
  subst h1; subst h2
  have eid : ∀ i (h : (PPx x').U i ≤ (𝟙 (Gx x')) ⁻¹ᵁ (PPx x').U i),
      Scheme.Hom.appLE (𝟙 (Gx x')) ((PPx x').U i) ((PPx x').U i) h = 𝟙 _ := by
    intro i h
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x').presheaf.map_id]
    rfl
  funext k
  apply Units.ext
  cases k with
  | none =>
    refine (g s').unique (fun i => ?_) (fun i => ?_)
    · exact (ha i le_rfl).symm.trans (congrArg (fun m => CommRingCat.Hom.hom m _) (eid i le_rfl))
    · exact (ha' i le_rfl).symm.trans (congrArg (fun m => CommRingCat.Hom.hom m _) (eid i le_rfl))
  | some k =>
    obtain ⟨τ, i⟩ := k
    obtain ⟨cf, h1, -, h3⟩ := hu τ i
    obtain ⟨cf', h1', -, h3'⟩ := hu' τ i
    have := (b τ (u' τ i) (tn' τ i) (e' τ i)).unique h3 h3'
    rw [← h1, ← h1', this]

end GlobalTheory.FrameRelCheck
