import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAmpleXF

theorem relAmple_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)) :
    SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  intro mF
  have hP : IsProper tF.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper
  obtain ⟨w, hw, -⟩ := mF.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ tF.G tF.PP.L tF.PP.isLB inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤)
    (x := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) s) trivial
  let f := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let U := f ⁻¹ᵁ V
  refine ⟨U, hs, ?_⟩
  have H : IsPullback ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (tF.G.hom ∣_ U) Xo.univ.t.G.hom (U.ι ≫ f) :=
    (isPullback_morphismRestrict tF.G.hom U).flip.paste_horiz mF.cart.1
  obtain ⟨w', hw'⟩ : LBIso (tF.PP.L.pull (tF.G.hom ⁻¹ᵁ U).ι) (Xo.univ.t.PP.L.pull ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ)) :=
    LBIso.chartPull (chartPullPull _ _)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => (tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (fun _ => mF.φ) (fun _ => 1)
        (tF.G.hom ⁻¹ᵁ U).ι fun _ => rfl) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (tF.G.hom ∣_ U)) H Xo.univ.t.PP.isLB (pull_isLB tF.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) Xo.univ.ample

end GlobalTheory.PullAmpleXF
