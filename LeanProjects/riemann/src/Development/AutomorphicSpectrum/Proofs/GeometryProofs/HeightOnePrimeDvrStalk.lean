import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem isDVR_of_ringKrullDim_eq_one (B : Type*) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (h : ringKrullDim B = 1) : IsDiscreteValuationRing B := by
  have hf : ¬ IsField B := fun hB => by
    rw [ringKrullDim_eq_zero_of_isField hB] at h
    exact zero_ne_one h
  have hle : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 (by rw [h]; rfl)
  have hmax := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hle
  have hT := (IsDiscreteValuationRing.TFAE B hf).out 0 3
  refine hT.2 ⟨inferInstance, ExistsUnique.intro (IsLocalRing.maximalIdeal B) ⟨?_, inferInstance⟩ ?_⟩
  · exact fun h0 => hf (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)
  · rintro Q ⟨h0, hQ⟩
    have := hmax Q h0 hQ
    exact IsLocalRing.eq_maximalIdeal this

theorem comap_maximalIdeal_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : PrimeSpectrum (X.presheaf.stalk y)) (hP : X.fromSpecStalk y P = x) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P.asIdeal := by
  have e := Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  have e3 : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x)) = x := by
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have e2 : X.fromSpecStalk y (Spec.map (X.presheaf.stalkSpecializes h)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))) = X.fromSpecStalk y P :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (e3.trans hP.symm)
  have inj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  exact congrArg PrimeSpectrum.asIdeal (inj e2)

theorem exists_mul_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : Ideal (X.presheaf.stalk y))
    (hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P)
    (b : X.presheaf.stalk x) :
    ∃ a, a ∉ P ∧ ∃ c, (X.presheaf.stalkSpecializes h).hom a * b = (X.presheaf.stalkSpecializes h).hom c := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have loc := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl b
  have hg : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U y hyU).hom r) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU h) r
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (t : Γ(X, U))) := IsLocalization.map_units _ t
  refine ⟨(X.presheaf.germ U y hyU).hom t, fun hm => ?_, (X.presheaf.germ U y hyU).hom r, ?_⟩
  · rw [← hP, Ideal.mem_comap, hg] at hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  · rw [hg, hg, mul_comm]
    exact ht

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem exists_generisation_of_height_eq_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hgen hN hnorm p P hP
  let P' : PrimeSpectrum (X.presheaf.stalk p.1) := ⟨Ideal.comap (regIso hgen p) P.asIdeal, inferInstance⟩
  have hP' : P'.asIdeal.height = 1 := ((regIso hgen p).height_comap P.asIdeal).trans hP
  have hmem : ∀ a, a ∈ P'.asIdeal ↔ regIso hgen p a ∈ P.asIdeal := fun a => Iff.rfl
  have hs : X.fromSpecStalk p.1 P' ⤳ p.1 := by
    have h : X.fromSpecStalk p.1 P' ∈ Set.range (X.fromSpecStalk p.1) := ⟨P', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hgq : genPt ξ ⤳ X.fromSpecStalk p.1 P' := by
    have e1 : genPt ξ = X.fromSpecStalk p.1 (spMap (genMap ξ p)
        (IsLocalRing.closedPoint Ω : Sp Ω)) :=
      (congrArg (fun g : Sp Ω ⟶ X => g (IsLocalRing.closedPoint Ω : Sp Ω))
        (spMap_genMap_fromSpecStalk p)).symm.trans (Scheme.Hom.comp_apply _ _ _)
    refine (specializes_of_eq e1).trans (Specializes.map ?_ (X.fromSpecStalk p.1).continuous)
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have h0 : genMap ξ p a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h0
    have : a = 0 := hgen.inj p (h0.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  let q : Cpt ξ := ⟨X.fromSpecStalk p.1 P', hgq⟩
  have hs' : q.1 ⤳ p.1 := hs
  obtain ⟨hdom, hic⟩ := hnorm q.1
  haveI := hN
  let f : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hs').hom
  have hcomap : (IsLocalRing.maximalIdeal (X.presheaf.stalk q.1)).comap f = P'.asIdeal :=
    comap_maximalIdeal_stalkSpecializes hs' P' rfl
  have hgf : ∀ a, genMap ξ q (f a) = genMap ξ p a := genMap_specializes hs'
  have hfinj : Function.Injective f := fun a b hab =>
    hgen.inj p (by rw [← hgf, ← hgf, hab])
  have hunit : ∀ a, a ∉ P'.asIdeal → IsUnit (f a) := fun a ha => by
    by_contra hu
    exact ha (hcomap ▸ (IsLocalRing.mem_maximalIdeal _).2 hu)
  have hfrac : ∀ b, ∃ a, a ∉ P'.asIdeal ∧ ∃ c, f a * b = f c :=
    exists_mul_stalkSpecializes hs' P'.asIdeal hcomap
  have hdim : ringKrullDim (X.presheaf.stalk q.1) = 1 := by
    letI : Algebra (X.presheaf.stalk p.1) (X.presheaf.stalk q.1) := f.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk q.1) P'.asIdeal :=
      { map_units := fun s => hunit s.1 s.2
        surj := fun b => by
          obtain ⟨a, ha, c, hc⟩ := hfrac b
          exact ⟨⟨c, ⟨a, ha⟩⟩, by rw [mul_comm]; exact hc⟩
        exists_of_eq := fun {a b} h => ⟨1, by rw [hfinj h]⟩ }
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P'.asIdeal (X.presheaf.stalk q.1), hP']
    rfl
  refine ⟨q, hs', ⟨hdom, isDVR_of_ringKrullDim_eq_one _ hdim⟩, fun s hsP => ?_, ?_⟩
  · have ha : (regIso hgen p).symm s ∉ P'.asIdeal := by
      rw [hmem, RingEquiv.apply_symm_apply]
      exact hsP
    obtain ⟨u, hu⟩ := (hunit _ ha).exists_right_inv
    refine ⟨u, ?_⟩
    refine eq_inv_of_mul_eq_one_right ?_
    have h1 := congrArg (genMap ξ q) hu
    rw [map_mul, map_one, hgf, genMap_regIso_symm] at h1
    exact h1
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, c, hc⟩ := hfrac b
    refine ⟨regIso hgen p a, fun h => ha ((hmem a).2 h), ⟨c, ?_⟩⟩
    have h1 := congrArg (genMap ξ q) hc
    rw [map_mul, hgf, hgf] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne
