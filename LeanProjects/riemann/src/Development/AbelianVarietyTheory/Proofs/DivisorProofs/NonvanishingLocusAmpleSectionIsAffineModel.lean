import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AffModel

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (g : X.functionField), 0 < e → g ∈ P.H e 0 → g ≠ 0 → ∃ (U : X.Opens) (h : genericPoint X ∈ U), (U : Set X) = NV P e 0 g ∧ IsAffineOpen U ∧ (∀ w : X.functionField, (∀ z ∈ U, RegAt z w) ↔ w ∈ (fnOf U h).range) ∧ Algebra.FiniteType ℤ (fnOf U h).range ∧ (∀ w : X.functionField, ∃ a ∈ (fnOf U h).range, ∃ b ∈ (fnOf U h).range, b ≠ 0 ∧ w = a / b) ∧ ∀ φ : (fnOf U h).range →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ U ∧ ∀ w : (fnOf U h).range, ratVal (w : X.functionField) y = φ w := by
  intro k _ X _ p D hV P hA e g he hg hg0
  obtain ⟨u, hu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P e).2 g hg
  have hN := GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P (e : ℤ) 0 g hg
  have : IsProper p := GlobalTheory.ProperFamily.isProper_of_isProjOver hV.isProjOver
  have hU : IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
  have hgen : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
    have := hN.2.1.2 hg0
    rw [hu] at this
    exact this
  set U := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u with hUdef
  have : Nonempty U := ⟨⟨_, hgen⟩⟩
  have hfr := functionField_isFractionRing_of_isAffineOpen X U hU
  refine ⟨U, hgen, hu.symm, hU, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hgen h
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩ z hz
      exact regAt_fnOf hz hgen a
  · have h1 : (algebraMap ℤ k).FiniteType := by
      have := hV.finite
      exact RingHom.finiteType_algebraMap.2 inferInstance
    have h2 : (p.appLE ⊤ U le_top).hom.FiniteType :=
      p.finiteType_appLE (isAffineOpen_top _) hU _
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩)
    have h4 : (fnOf U hgen).rangeRestrict.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fnOf U hgen).rangeRestrict_surjective
    have h5 := h4.comp (h2.comp (h3.comp h1))
    rw [← RingHom.finiteType_algebraMap]
    convert h5
    exact RingHom.ext_int _ _
  · intro w
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) w
    refine ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, ?_, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hb (fnOf_injective U hgen (h0.trans (map_zero _).symm))
    · exact hab.symm
  · intro φ
    let ψ : Γ(X, U) →+* ℂ := φ.comp (fnOf U hgen).rangeRestrict
    refine ⟨ψ.comp (algX p U), CxPts.ofHom hU ψ (fun _ => rfl), mem_ptsIn.1 (CxPts.ofHom_mem hU ψ _), ?_⟩
    rintro ⟨_, a, rfl⟩
    rw [ratVal_fnOf (CxPts.ofHom_mem hU ψ _) hgen a, CxPts.ev_ofHom]
    rfl

end GlobalTheory.AffModel
