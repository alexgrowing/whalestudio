import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUnitaryPointGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTraitExt

theorem exists_ext_unif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁]
    (hV : CDvr V₁) (y₁ : Sp (FractionRing V₁) ⟶ Xo.XF c) (t : SAB H (Sp V₁)) (hg : GenOf Xo c y₁ t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
      (fK : FractionRing V₁ →+* FractionRing W), CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
      ∃ t' : SAB H (Sp W), GenOf Xo c (spMap fK ≫ y₁) t' ∧ Nonempty (PELUnif (maximalIdeal W) t') := by
  obtain ⟨hdvr, hc, hz⟩ := hV
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := hg
  let T : Formalism.L2.Pj.CDVR := @Formalism.L2.Pj.CDVR.mk V₁ _ _ hdvr hc hz
  obtain ⟨T', φ, t', m', hi, hf, ⟨P⟩⟩ :=
    GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T t tK mK (y₁ ≫ pullback.fst _ _) mx
  let fK : FractionRing V₁ →+* FractionRing T'.V :=
    IsFractionRing.map (A := V₁) (B := T'.V) (K := FractionRing V₁) (L := FractionRing T'.V) hi
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap T'.V _ (φ a) := fun a => IsLocalization.map_eq _ _
  have hsq : spMap fK ≫ jK V₁ = jK T'.V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hfK a
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull Out.CubePf.cubePull (spMap fK) tK
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mK n
  rw [hsq] at b
  obtain ⟨mK', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m' b
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx n
  have hloc : IsLocalHom φ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  refine ⟨T'.V, inferInstance, inferInstance, inferInstance, φ, fK, ⟨inferInstance, inferInstance, inferInstance⟩, hi,
    hloc, hf, hfK, t', ⟨_, ⟨mK'⟩, ⟨?_⟩⟩, ⟨P⟩⟩
  rw [Category.assoc]
  exact mx'

end GlobalTheory.UTraitExt

namespace GlobalTheory.UTraitExt

theorem uTraitExtSt : UTraitExtSt := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  obtain ⟨V₁, _, _, _, f₁, fK₁, hC₁, hi₁, hl₁, hf₁, hc₁, t₁, hg₁⟩ := GlobalTheory.T.exists_finite_extension_unitary_point_generic_fibre E H Dw l Xo c V hB hV y
  obtain ⟨W, _, _, _, f₂, fK₂, hC₂, hi₂, hl₂, hf₂, hc₂, t, hg, ⟨P⟩⟩ := exists_ext_unif Xo c V₁ hC₁ _ t₁ hg₁
  haveI : IsDiscreteValuationRing W := hC₂.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg' : GenOf Xo c (spMap fK₂ ≫ spMap fK₁ ≫ y) t := by rw [← Category.assoc]; exact hg
  obtain ⟨be, hbe, hmono⟩ := GlobalTheory.MonPeriods.exists_isMonomial_levelOne hC₂ ϖ hϖ t P
  have hy : spMap fK₂ ≫ spMap fK₁ ≫ y = spMap (fK₂.comp fK₁) ≫ y := by
    rw [← Category.assoc]; congr 1
    simp [spMap, ← Spec.map_comp]
  let T : UTrait Xo c :=
    { V := W
      cdvr := hC₂
      ϖ := ϖ
      irr := hϖ
      y := spMap fK₂ ≫ spMap fK₁ ≫ y
      t := t
      gen := hg'
      P := P
      be := be
      lev := hbe
      mono := hmono }
  refine ⟨T, f₂.comp f₁, fK₂.comp fK₁, hi₂.comp hi₁, ?_, hf₂.comp hf₁, fun a => ?_, hy⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · show fK₂ (fK₁ _) = _
    rw [hc₁, hc₂]
    rfl

end GlobalTheory.UTraitExt
