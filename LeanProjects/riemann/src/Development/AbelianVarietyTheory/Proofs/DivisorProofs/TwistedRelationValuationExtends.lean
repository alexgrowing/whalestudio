import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecOfAnypoint

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry

theorem ptRel_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] (ν : V →+* L) (k : Type) [Field k] (r : V →+* k) (q : Sp V ⟶ C.Y.X) (q' : Sp V ⟶ C'.Y.X), Function.Injective ν → RingHom.ker r = IsLocalRing.maximalIdeal V → T.PtRel C C' (spMap ν ≫ q) (spMap ν ≫ q') → T.PtRel C C' (spMap r ≫ q) (spMap r ≫ q') := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ e C C' V _ _ _ L _ ν k _ r q q' hν hr ⟨hπ, χ, f, f', hχ, hP, hC, hC'⟩
  have : IsDominant (spMap ν) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ν).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hν]; exact bot_le)⟩
  have : IsProper Z.s := by
    obtain ⟨N, i, _, h⟩ := Z.proj
    have := isProper_str O N
    rw [← h]
    infer_instance
  have : (gen Z).IsSeparated := ⟨by rw [← Limits.terminal.comp_from (genStr Z)]; infer_instance⟩
  have hq' : q' ≫ C'.π = q ≫ C.π ≫ T.g.hom :=
    ext_of_isDominant (spMap ν) (by simpa only [Category.assoc] using hπ)

  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f₁, t₁, hf₁, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [CarrySpec.spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := CarriesAt.tri_of_carries E H Dw l Xo c O β Z F e C L χ _ f (spMap ν ≫ q) hC y₀ (ν.comp ρ) φ₁ f₁ t₁
    hpL hf₁
  have hxV : q ≫ C.π ≫ genι Z = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    (congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _)
  obtain ⟨gV, hgV⟩ := f₁.exists_isMap (φ' := ρ.comp φ₁) ρ rfl hxV
  have hχν : χ = ν.comp (ρ.comp φ₁) := hfL.2.1
  have hxL : (spMap ν ≫ q) ≫ C.π ≫ genι Z = spMap ν ≫ q ≫ C.π ≫ genι Z := Category.assoc _ _ _
  obtain ⟨gL, hgL⟩ := gV.exists_isMap ν hχν hxL
  have hco := fun τ => EigFrame.Tri.co τ hfL (CarrySpec.isMap_comp hgV hgL)
  have hV : gV.Tri ν f t' := CarrySpec.tri_of_co hgL hxL hχν t' (fun τ => (hco τ).1) fun τ => (hco τ).2

  have hx' : q' ≫ C'.π ≫ genι Z = (q ≫ C.π ≫ genι Z) ≫ T.ρ.hom := by
    rw [← Category.assoc, hq']
    simp only [Category.assoc, T.g_ι]
  obtain ⟨gV', hPV⟩ := T.exists_push (φ' := ρ.comp φ₁) gV rfl hx'
  have hV' : gV'.Tri ν f' fun τ i => t' (T.emb τ) (T.ix i) := (hPV.tri_iff hP fun _ _ => rfl).1 hV

  have hxk : (spMap r ≫ q) ≫ C.π ≫ genι Z = spMap r ≫ q ≫ C.π ≫ genι Z := Category.assoc _ _ _
  have hxk' : (spMap r ≫ q') ≫ C'.π ≫ genι Z = spMap r ≫ q' ≫ C'.π ≫ genι Z := Category.assoc _ _ _
  obtain ⟨gk, hgk⟩ := gV.exists_isMap (φ' := r.comp (ρ.comp φ₁)) r rfl hxk
  obtain ⟨gk', hgk'⟩ := gV'.exists_isMap (φ' := r.comp (ρ.comp φ₁)) r rfl hxk'
  have hstr : q ≫ C.π ≫ genStr Z = spMap (ρ.comp φ₁) :=
    ext_of_isDominant (spMap ν) (by rw [← CarrySpec.spMap_comp, ← hχν, ← hχ, Category.assoc])
  refine ⟨by rw [Category.assoc, hq', Category.assoc], r.comp (ρ.comp φ₁), gk, gk', ?_, hPV.map hgk hgk' rfl ?_, ?_, ?_⟩
  · rw [Category.assoc, hstr, ← CarrySpec.spMap_comp]
  · rw [hxk', hxk, hx']
    simp only [Category.assoc]
  · exact CarrySpec.spec_of_anypoint CarriesAt.tri_of_carries E H Dw l Xo c O β Z F e C V L ν hν k r hr q _ _ rfl gV _ _ f _
      hV hC _ _ gk _ (hgk.tri rfl hxk)
  · exact CarrySpec.spec_of_anypoint CarriesAt.tri_of_carries E H Dw l Xo c O β Z F e C' V L ν hν k r hr q' _ _ rfl gV' _ _
      f' _ hV' hC' _ _ gk' _ (hgk'.tri rfl hxk')

end GlobalTheory.ShFam.GalCarry
