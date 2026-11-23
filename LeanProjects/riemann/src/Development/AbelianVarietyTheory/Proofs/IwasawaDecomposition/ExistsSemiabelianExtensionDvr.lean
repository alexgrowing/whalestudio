import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.TraitUnif

theorem exists_ext_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (t' : SAB H (Sp W')) (_ : SABMap t' Y.t (spMap ι ≫ χ)) (_ : PELUnif (maximalIdeal W') t'), CDvr W' ∧ Function.Injective ι ∧ IsLocalHom ι := by
  intro E _ _ _ H D l Xo c Y W _ _ _ hW χ hgen
  obtain ⟨hdvr, hc, hz⟩ := hW
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have hj : IsOpenImmersion Y.j := by
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  let x₀ : Sp (FractionRing W) ⟶ Xo.XF c := IsOpenImmersion.lift Y.j (jK W ≫ χ) hgen
  have hx₀ : x₀ ≫ Y.j = jK W ≫ χ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨PP, cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull x₀ Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hx₀' : x₀ ≫ Y.jQ ≫ pullback.fst _ _ = jK W ≫ χ := hx₀
  rw [hx₀'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  let T : Formalism.L2.Pj.CDVR := @Formalism.L2.Pj.CDVR.mk W _ _ hdvr hc hz
  obtain ⟨T', φ, t', m', hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T _ _ mK _ mx
  obtain ⟨m'', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have hloc : IsLocalHom φ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  exact ⟨T'.V, inferInstance, inferInstance, inferInstance, φ, t', m'', P, ⟨inferInstance, inferInstance, inferInstance⟩, hi, hloc⟩

end GlobalTheory.TraitUnif
