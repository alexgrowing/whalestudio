import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ModelPointExt

theorem exists_integral_extension {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K]
    (jF : c.F →+* K) (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z)
    (hy : yK ≫ GlobalTheory.Toroidal.genStr Z = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jF) :
    ∃ yO : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K) ⟶ Z.X,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap (𝓞 K) K) ≫ yO = yK ≫ GlobalTheory.Toroidal.genι Z := by
  let jO : 𝓞 c.F →+* 𝓞 K := RingOfIntegers.mapRingHom jF
  have hring : (algebraMap (𝓞 K) K).comp jO = jF.comp (algebraMap (𝓞 c.F) c.F) := by
    ext x; rfl
  haveI : IsProper Z.s := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap Z
  let X' : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K)) := Over.mk (pullback.snd Z.s (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jO))
  have hP : IsProper X'.hom := by
    show IsProper (pullback.snd Z.s (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jO))
    infer_instance
  have hsq : (yK ≫ GlobalTheory.Toroidal.genι Z) ≫ Z.s =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap (𝓞 K) K) ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jO := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [hring]
  let x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X'.left := pullback.lift _ _ hsq
  have hx : x ≫ X'.hom = Formalism.L2.Pj.abelian₂.gmap K := pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ := GlobalTheory.CuspFamilyCompare.exists_integral_point K X' hP x hx
  refine ⟨s.left ≫ pullback.fst _ _, ?_⟩
  have : x ≫ pullback.fst _ _ = yK ≫ GlobalTheory.Toroidal.genι Z := pullback.lift_fst _ _ _
  rw [← this, hs, Category.assoc]

end GlobalTheory.ModelPointExt
