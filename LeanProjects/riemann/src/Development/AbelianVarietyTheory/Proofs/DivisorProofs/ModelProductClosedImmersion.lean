import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.ModelClosure

set_option backward.isDefEq.respectTransparency false in

theorem flat_of_isIntegral {O : Type} [CommRing O] [IsDedekindDomain O] {X : Scheme.{0}}
    [IsIntegral X] (s : X ⟶ Sp O) (x : X) (hx : (s x).asIdeal = ⊥) : Flat s := by
  have hξ : (s (genericPoint X)).asIdeal = ⊥ := by
    have h := (genericPoint_specializes x).map s.continuous
    rw [← PrimeSpectrum.le_iff_specializes] at h
    exact le_bot_iff.1 (hx ▸ h)
  have hsup : ⨆ U : {U : X.affineOpens // ((U : X.Opens) : Set X).Nonempty}, (U.1 : X.Opens) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : y ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, y, hU⟩, hU⟩
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat)
    (fun U : {U : X.affineOpens // ((U : X.Opens) : Set X).Nonempty} ↦ U.1) hsup fun U ↦ ?_
  obtain ⟨⟨U, hUa⟩, ⟨u, hu⟩⟩ := U
  haveI : Nonempty (U : X.Opens) := ⟨⟨u, hu⟩⟩
  rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of O)).inv]
  letI := ((s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of O)).inv.hom).toAlgebra
  refine (IsDedekindDomain.flat_iff_torsion_eq_bot (R := O) (M := Γ(X, U))).mpr ?_
  rw [eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, ha⟩
  have ha' : s.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of O)).inv r) * a = 0 := ha
  refine (mul_eq_zero.1 ha').resolve_left fun h0 => ?_
  have hb := Scheme.basicOpen_appLE s U ⊤ le_top ((Scheme.ΓSpecIso (.of O)).inv r)
  rw [h0, Scheme.basicOpen_zero] at hb
  have hmem : genericPoint X ∈ (U : X.Opens) ⊓ s ⁻¹ᵁ (Sp O).basicOpen ((Scheme.ΓSpecIso (.of O)).inv r) := by
    refine ⟨?_, ?_⟩
    · exact ((genericPoint_specializes u).mem_open U.isOpen hu)
    · show s (genericPoint X) ∈ (Sp O).basicOpen ((Scheme.ΓSpecIso (.of O)).inv r)
      rw [basicOpen_eq_of_affine]
      show r ∉ (s (genericPoint X)).asIdeal
      rw [hξ]
      exact nonZeroDivisors.ne_zero hr
  rw [← hb] at hmem
  exact hmem

theorem map_genericPoint {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] (g : Y ⟶ Y')
    [Surjective g] : g (genericPoint Y) = genericPoint Y' := by
  have h := (genericPoint_spec Y).image g.continuous
  rw [Set.image_univ, g.surjective.range_eq, closure_univ] at h
  exact h.eq (genericPoint_spec Y')

theorem surjective_of_genericPoint {Y Y' : Scheme.{0}} [IsIntegral Y'] (g : Y ⟶ Y')
    (hg : IsClosedMap g) (y : Y) (hy : g y = genericPoint Y') : Surjective g := by
  refine ⟨fun t => ?_⟩
  have h : closure {genericPoint Y'} ⊆ Set.range g :=
    closure_minimal (by rintro _ rfl; exact ⟨y, hy⟩) hg.isClosed_range
  have h2 := (genericPoint_spec Y').def
  exact h (h2 ▸ Set.mem_univ t)

end GlobalTheory.ModelClosure

namespace GlobalTheory.ModelClosure

theorem exists_model_closedImmersion_pullback : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B B₁ B₂ : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B),
    ∃ (Z : GlobalTheory.Vert.Model O) (h₁ : GlobalTheory.Vert.Model.Hom Z B₁) (h₂ : GlobalTheory.Vert.Model.Hom Z B₂)
      (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f), IsClosedImmersion (pullback.lift h₁.f h₂.f w) := by
  intro O _ _ _ B B₁ B₂ f₁ f₂
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f₁.f) (g := f₂.f)
    (genericPoint B₁.X) (genericPoint B₂.X) ((map_genericPoint f₁.f).trans (map_genericPoint f₂.f).symm)
  let j := (pullback f₁.f f₂.f).fromSpecResidueField z
  obtain ⟨ζ, hζ⟩ : z ∈ Set.range j.imageι := by
    rw [GlobalTheory.range_imageι j, Scheme.range_fromSpecResidueField]
    exact subset_closure rfl
  let ι := j.imageι
  let s := ι ≫ pullback.fst f₁.f f₂.f ≫ B₁.str
  have hproj : IsProjOver s := by
    have e : s = (ι ≫ pullback.mapDesc f₁.f f₂.f B.str) ≫
        pullback.fst (f₁.f ≫ B.str) (f₂.f ≫ B.str) ≫ f₁.f ≫ B.str := by
      simp only [s, pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_fst_assoc, Category.comp_id, f₁.comp_str]
    rw [e]
    refine GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ ?_
    refine GlobalTheory.ProjSpace.isProjOver_pullback ?_ ?_
    · rw [f₁.comp_str]; exact B₁.isProjOver
    · rw [f₂.comp_str]; exact B₂.isProjOver
  have hs : s ζ = B₁.str (genericPoint B₁.X) := by
    show B₁.str (pullback.fst f₁.f f₂.f (ι ζ)) = _
    rw [show ι ζ = z from hζ, hz₁]
  have hflat : Flat s := flat_of_isIntegral s ζ (by
    rw [hs]; exact GlobalTheory.Vert.Model.mem_gen_iff_eq_bot.1 B₁.genericPoint_mem_gen)
  let Z : GlobalTheory.Vert.Model O :=
    { X := j.image, str := s, isIntegral := inferInstance, isProjOver := hproj, flat := hflat }
  haveI : IsProper f₁.f := GlobalTheory.Vert.Model.isProper_of_comp_str f₁.comp_str
  haveI : IsProper f₂.f := GlobalTheory.Vert.Model.isProper_of_comp_str f₂.comp_str
  let h₁ : GlobalTheory.Vert.Model.Hom Z B₁ :=
    { f := ι ≫ pullback.fst f₁.f f₂.f
      comp_str := by simp [Z, s]
      surjective := surjective_of_genericPoint _ (ι ≫ pullback.fst f₁.f f₂.f).isClosedMap ζ
        (by show pullback.fst f₁.f f₂.f (ι ζ) = _; rw [show ι ζ = z from hζ, hz₁]) }
  let h₂ : GlobalTheory.Vert.Model.Hom Z B₂ :=
    { f := ι ≫ pullback.snd f₁.f f₂.f
      comp_str := by
        simp only [Z, s, Category.assoc, ← f₂.comp_str, ← f₁.comp_str]
        rw [pullback.condition_assoc]
      surjective := surjective_of_genericPoint _ (ι ≫ pullback.snd f₁.f f₂.f).isClosedMap ζ
        (by show pullback.snd f₁.f f₂.f (ι ζ) = _; rw [show ι ζ = z from hζ, hz₂]) }
  have w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f := by
    simp only [h₁, h₂, Category.assoc, pullback.condition]
  refine ⟨Z, h₁, h₂, w, ?_⟩
  have e : pullback.lift h₁.f h₂.f w = ι := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  rw [e]
  infer_instance

end GlobalTheory.ModelClosure
