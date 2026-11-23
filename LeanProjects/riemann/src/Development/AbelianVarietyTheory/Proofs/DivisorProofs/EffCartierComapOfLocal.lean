import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorialLocus

open ReciprocityTheory.AnForm.R

theorem exists_affine_gen {X : Scheme.{0}} [IsLocallyNoetherian X] (G : X.IdealSheafData) (x : X)
    (t : X.presheaf.stalk x) (htnzd : t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (ht : FinalTheorems.stalkId G x = Ideal.span {t}) :
    ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧
      G.ideal U = Ideal.span {f} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(X, U) (X.presheaf.stalk x) a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(X, X.basicOpen σ)
  refine ⟨X.affineBasicOpen (U := U') σ, algebraMap Γ(X, U) Γ(X, X.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ X.basicOpen σ
    rw [X.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem stalkId_eq_span_of_mem {X : Scheme.{0}} (G : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1)) (hG : G.ideal U = Ideal.span {f})
    (y : X) (hy : y ∈ U.1) :
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk y), FinalTheorems.stalkId G y = Ideal.span {t} := by
  refine ⟨X.presheaf.germ U.1 y hy f, ?_, ?_⟩
  · letI : Algebra Γ(X, U.1) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hy⟩
    haveI := U.2.isLocalization_stalk ⟨y, hy⟩
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hf
  · rw [ds_stalkId_eq_map G U y hy, hG, Ideal.map_span, Set.image_singleton]

theorem effCartier_comap_of_local {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f]
    (hI : ∀ x : X, ∃ (U : Y.affineOpens) (h : Γ(Y, U.1)), f x ∈ U.1 ∧
      h ∈ nonZeroDivisors Γ(Y, U.1) ∧ I.ideal U = Ideal.span {h}) :
    FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI x
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem exists_isLocus : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (V : X.Opens), IsAffineOpen V → (V : Set X).Nonempty → ∃ W : X.Opens, V ≤ W ∧ (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W) ∧ ∃ c : Pic W.toScheme, IsLocus c (W.ι ⁻¹ᵁ V) := by
  intro X _ _ _ V hV hne
  have hι : IsAffineHom V.ι :=
    haveI : IsAffine V := hV
    haveI : IsAffineHom (V.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  let G := Scheme.IdealSheafData.vanishingIdeal V.compl
  let P : X → Prop := fun x =>
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}
  have hopen : IsOpen {x | P x} := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨t, ht, htG⟩ := hx
    obtain ⟨U, f, hxU, hf, hG⟩ := exists_affine_gen G x t ht htG
    exact ⟨U.1, fun y hy => stalkId_eq_span_of_mem G U f hf hG y hy, U.1.isOpen, hxU⟩
  let W : X.Opens := ⟨{x | P x}, hopen⟩
  have hVW : V ≤ W := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ (1 : X.presheaf.stalk x) ∉ q.asIdeal := fun q => by
      refine iff_of_true ?_ fun h1 => q.2.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      have hs : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hs
      exact Specializes.mem_open hs V.isOpen hx
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x 1 h, Ideal.span_singleton_one,
      Ideal.radical_top]
  have hfac : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W := by
    intro x hufd
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) V) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqV : q ∈ X.fromSpecStalk x ⁻¹ᵁ V := by
      change X.fromSpecStalk x q ∈ V
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
      (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn hufd
      (X.fromSpecStalk x ⁻¹ᵁ V) hA ⟨q, hqV⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqV (h0 ▸ zero_mem _)
    show P x
    simp only [P, G]
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x a h]
    exact GlobalTheory.AffineComplement.exists_radical_span_singleton_eq ha0
  refine ⟨W, hVW, hfac, ?_⟩
  have hE : FinalTheorems.EffCartier (G.comap W.ι) := by
    refine effCartier_comap_of_local G W.ι fun y => ?_
    have hy : P (W.ι y) := y.2
    obtain ⟨t, ht, htG⟩ := hy
    exact exists_affine_gen G _ t ht htG
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨cls D.lb D.isLB_lb, D.lb, D.isLB_lb, D.canonical, rfl, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  ext y
  simp

end GlobalTheory.FactorialLocus
