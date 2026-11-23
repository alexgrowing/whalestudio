import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeInFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtaleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReducedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocallyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbasesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEtaleCoverListingHeckeKernelSchemeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCuspSectionsOfDominatedRationalIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTermsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamilyStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

section Sec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

abbrev term (P : Ideal (𝓞 E)) (p i : ℕ) (f : Rul Xo c) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) : Ω :=
  hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y C

theorem bc_exists {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

theorem bc_unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') : z = z' :=
  (frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

theorem isHeckeIsog_unique (hA : admitted l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x₁ x₂ : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ₁ : Gx x ⟶ Gx x₁} {ψ₂ : Gx x ⟶ Gx x₂}
    (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C) (h₁ : IsHeckeIsog p C ψ₁) (h₂ : IsHeckeIsog p C ψ₂) :
    x₁ = x₂ ∧ HEq ψ₁ ψ₂ := by
  have hc : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  obtain ⟨ψ₁, rfl⟩ := (GlobalTheory.HeckeFrCompare.conj x x₁).surjective ψ₁
  obtain ⟨ψ₂, rfl⟩ := (GlobalTheory.HeckeFrCompare.conj x x₂).surjective ψ₂
  obtain ⟨f₁, k₁⟩ := (GlobalTheory.HeckeFrCompare.isog_iff hc _ _ _ _).2 h₁
  obtain ⟨f₂, k₂⟩ := (GlobalTheory.HeckeFrCompare.isog_iff hc _ _ _ _).2 h₂
  obtain ⟨-, a, b⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2 hC k₂
  obtain rfl := a _ _ _ k₁
  obtain rfl := b _ _ k₁
  exact ⟨rfl, HEq.rfl⟩

theorem exists_card_heckeKer_le (hA : admitted l P p) : ∃ M : ℕ, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ Xo.X),
    Nat.card {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C} ≤ M := by
  have hp := hA.2.2.1.pos
  refine ⟨2 ^ (p ^ 2) ^ (2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))), fun Ω _ _ x => ?_⟩
  have h₀ : Nat.card (Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})) = _ :=
    (HeckeKerModel.heckeKer_zero Xo.univ Ω x _ (Spec.map_preimage (x ≫ Xo.s)).symm P (p ^ 2)
      (pow_pos hp 2)).2.2.2.2.1
  have hf : Finite (Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})) :=
    Nat.finite_of_card_ne_zero (h₀.trans_ne (pow_ne_zero _ (pow_pos hp 2).ne'))
  have hs : ∀ C : {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C}, ∀ z ∈ C.1,
      z ∈ Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) := fun C z hz a ha => by
    refine C.2.2.2.1 hz a ((Ideal.span_singleton_le_iff_mem _).2 ?_ ha)
    rw [Nat.cast_pow, pow_two]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hA.2.2.2.1
    rwa [map_natCast] at this
  refine (Nat.card_le_card_of_injective
    (β := Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) → Prop) (fun C z => z.1 ∈ C.1)
    fun C C' e => Subtype.ext (Subgroup.ext fun z => ⟨fun h => ?_, fun h => ?_⟩)).trans_eq ?_
  · exact (congrFun e ⟨z, hs C z h⟩).mp h
  · exact (congrFun e ⟨z, hs C' z h⟩).mpr h
  · rw [Nat.card_fun, h₀, Nat.card_eq_fintype_card, Fintype.card_prop]

theorem hkPt_along (hA : admitted l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    {y z : FrPt Xo c Ω} {x' : Sp Ω ⟶ Xo.X} {Ψ : Gx y.x ⟶ Gx x'} {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)}
    (hC : Xo.univ.t.HeckeKer (Over.mk y.x) Dw P p i C) (hΨ : IsHeckeIsog p C Ψ) (hz : HkPt p (hkTr Xo c p Ω) y C z) :
    ∃ h : z.x = x', (∀ τ j, IsLieImg p Ψ (y.u τ j) (z.u τ j)) ∧
      IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p y.s (h ▸ z.s) := by
  obtain ⟨ψ, h₁, h₂, h₃⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hA _ y C z).1 hz
  obtain ⟨rfl, e⟩ := isHeckeIsog_unique hA hC h₁ hΨ
  obtain rfl := eq_of_heq e
  rw [hkTr, Equiv.apply_symm_apply] at h₃
  exact ⟨rfl, h₂, h₃⟩

theorem exists_term_of_family (hA : admitted l P p) (hT : TotalAt Xo c P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : Type} [CommRing T] [IsReduced T]
    [Algebra c.F T] (y : FrPt Xo c T) {x' : Sp T ⟶ Xo.X} (hx' : x' ≫ Xo.s = sOf c T) {Ψ : Gx y.x ⟶ Gx x'}
    (hΨ : IsHeckeFam P p i Ψ) {m : ℕ} {σ : Fin m → (Over.mk y.x ⟶ Xo.univ.t.G)} (hσ : IsListed Ψ σ)
    {s₀ : LB.Sec (PPx x')} (hs₀ : SecGen x' s₀) :
    ∃ b : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
      (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (C : hkKer (Xo := Xo) P p i Ω y₁), FrMap χ y y₁ →
      IsFib χ.toRingHom Ψ Ψ₁ → C.1 = transKer Xo.univ.t.G Ψ₁ → χ b = term P p i f y₁ C := by
  have hp : p ≠ 0 := hA.2.2.1.ne_zero
  obtain ⟨u, hu, he, hb⟩ := GlobalTheory.T.etale_linear_hom_framed_point_eigenbases E H Dw l Xo c T y x' Ψ p hp hΨ.1 hΨ.2.1
  let z₀ : FrPt Xo c T := ⟨x', hx', u, fun τ j => (hu τ j).2.1, he, hb, s₀, hs₀⟩
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family E H Dw l Xo c P p i m T y x' Ψ σ s₀ hA hΨ hσ hs₀ (fun Ω _ _ _ χ y₁ x₁' Ψ₁ _ hF => by
    obtain ⟨hC, hI⟩ := hΨ.2.2.2.2 Ω _ _ _ Ψ₁ hF
    obtain ⟨z, hz⟩ := hT Ω y₁ ⟨_, hC⟩
    obtain ⟨rfl, -, h⟩ := hkPt_along hA hC hI hz
    exact ⟨z.s, z.gen, h⟩)
  refine ⟨a₀ ^ n * evR Xo c f z₀, fun Ω _ _ _ χ y₁ x₁' Ψ₁ C hy hF hC => ?_⟩
  obtain ⟨-, hI⟩ := hΨ.2.2.2.2 Ω _ _ _ Ψ₁ hF
  have hex := hT Ω y₁ C
  rw [term, hkTerm, dif_pos hex]
  have hz := hex.choose_spec
  generalize hex.choose = z at hz ⊢
  obtain ⟨rfl, h₁, h₂⟩ := hkPt_along hA C.2 (hC ▸ hI) hz
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  refine (GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator E H Dw l Xo c a n f hf T Ω χ z₀ z a₀ ?_ (fun τ j => ?_)
    (ha₀ Ω χ y₁ z.x Ψ₁ z.s hy hF z.gen h₂)).symm
  · obtain ⟨_, _, _, h, _⟩ := hF
    exact h.1
  · refine GlobalTheory.T.lie_divided_hom_tangent_image_baseChange E H Dw l Xo T Ω _ _ _ _ _ Ψ Ψ₁ p _ _ _ (Nat.cast_ne_zero.2 hp).isUnit hF (hu τ j) ?_
    rw [← hy.2.1]
    exact h₁ τ j

theorem exists_term (hA : admitted l P p) (hT : TotalAt Xo c P p i) (Z : Corr Xo P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {B : Type} [CommRing B] [IsReduced B]
    [Algebra c.F B] (y : FrPt Xo c B) (h : Sp B ⟶ Z.Hk) (hh : h ≫ Z.π₁ = y.x) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
      (C : hkKer (Xo := Xo) P p i Ω y₁), FrMap χ y y₁ → Z.toKerScheme.Carries (spMap χ.toRingHom ≫ h) y₁.x C.1 →
      χ b = term P p i f y₁ C := by
  choose bc hbc using fun (Ω : Type) [Field Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω) => bc_exists χ y
  choose e he using GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels E H Dw l Xo P p i Z.toKerScheme hA
  have hw : ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω),
      (spMap χ.toRingHom ≫ h) ≫ Z.π₁ = (bc Ω χ).x := fun Ω _ _ χ => by
    rw [Category.assoc, hh, (hbc Ω χ).1]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_function_of_smooth_local_descent_reduced c.F B (fun Ω _ _ _ χ => term P p i f (bc Ω χ) (e Ω _ ⟨_, hw Ω χ⟩)) (fun q => by
    obtain ⟨T', _, _, m, σ, hT', hs, hσ, hl⟩ := GlobalTheory.T.exists_etale_cover_listing_heckeKernelScheme E H Dw l Xo P p i Z.toKerScheme hA B h
    obtain ⟨q', rfl⟩ := hs q
    letI : Algebra c.F T' := ((algebraMap B T').comp (algebraMap c.F B)).toAlgebra
    haveI : IsScalarTower c.F B T' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hso : ∀ (T : Type) [CommRing T] [Algebra c.F T] [Algebra B T] [IsScalarTower c.F B T],
        (spMap (algebraMap B T) ≫ h ≫ Z.π₂) ≫ Xo.s = sOf c T := fun T _ _ _ _ => by
      rw [Category.assoc, Category.assoc, Z.base₂, reassoc_of% hh, y.x_over, sOf, sOf, ChgBC.spMap_comp_ring,
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    obtain ⟨g, hg, s₀, hs₀⟩ := GlobalTheory.T.exists_thetaLine_generator_zariski_locally E H Dw l Xo c T' _ (hso T') q'
    let T := Localization.Away g
    have hsm : Algebra.Smooth B T := by
      have : Algebra.Smooth T' T := Algebra.Smooth.of_isLocalization_Away g
      exact Algebra.Smooth.comp B T' T
    have hred : IsReduced T := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B T
    have e₁ : spMap (algebraMap T' T) ≫ spMap (algebraMap B T') = spMap (algebraMap B T) := by
      rw [ChgBC.spMap_comp_ring, ← IsScalarTower.algebraMap_eq]
    obtain ⟨yT, hyT⟩ := bc_exists (IsScalarTower.toAlgHom c.F B T) y
    have hx : yT.x = (spMap (algebraMap B T) ≫ h) ≫ Z.π₁ := by rw [Category.assoc, hh]; exact hyT.1
    obtain ⟨Ψ, hΨ, hc⟩ := GlobalTheory.T.exists_heckeIsogenyFamily_pullback_correspondence E H Dw l Xo P p i Z hA T (spMap (algebraMap B T) ≫ h) yT.x
      (spMap (algebraMap T' T) ≫ spMap (algebraMap B T') ≫ h ≫ Z.π₂) hx (by rw [reassoc_of% e₁, Category.assoc])
    obtain ⟨b', hb'⟩ := exists_term_of_family hA hT hf yT (by rw [reassoc_of% e₁]; exact hso T) hΨ
      (σ := fun j => Over.homMk (spMap (algebraMap T' T) ≫ σ j) (by
        show _ = yT.x
        rw [Category.assoc, hσ, reassoc_of% e₁, hx, Category.assoc]))
      (fun Ω _ _ χ x₁ x₁' Ψ₁ hF => by
        obtain ⟨k, hk⟩ := hl Ω (χ.comp (algebraMap T' T)) x₁ (transKer _ Ψ₁) (by
          rw [← ChgBC.spMap_comp_ring, Category.assoc, reassoc_of% e₁]
          exact hc Ω χ _ _ Ψ₁ hF)
        exact ⟨k, fun j => by rw [hk, ← ChgBC.spMap_comp_ring, Category.assoc]; rfl⟩) hs₀
    refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, b', hsm, ?_, fun Ω _ _ _ χ => ?_⟩
    · obtain ⟨q'', rfl⟩ : q' ∈ Set.range (PrimeSpectrum.comap (algebraMap T' T)) := by
        rw [PrimeSpectrum.localization_away_comap_range T g]
        exact hg
      exact ⟨q'', by rw [IsScalarTower.algebraMap_eq B T' T]; rfl⟩
    · have hm : FrMap χ yT (bc Ω (χ.comp (IsScalarTower.toAlgHom c.F B T))) := by
        obtain ⟨w, hw⟩ := bc_exists χ yT
        rwa [bc_unique (hbc Ω _) (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ y yT w hyT hw)]
      obtain ⟨Ψ₁, hF⟩ := exists_isFib χ.toRingHom hm.1 rfl Ψ hΨ.1.1
      refine hb' Ω χ _ _ Ψ₁ _ hm hF ((he Ω _ ⟨_, hw Ω _⟩ _).1 ?_).symm
      have := hc Ω _ _ _ Ψ₁ hF
      rwa [← Category.assoc, ChgBC.spMap_comp_ring] at this)
  refine ⟨b, fun Ω _ _ _ χ y₁ C hy hC => ?_⟩
  obtain rfl := bc_unique hy (hbc Ω χ)
  rw [hb, show C = e Ω _ ⟨_, hw Ω χ⟩ from Subtype.ext ((he Ω _ ⟨_, hw Ω χ⟩ _).1 hC)]

theorem exists_sum (hr : 1 ≤ Dw.p + Dw.q) (hA : admitted l P p) (hT : TotalAt Xo c P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {R : Type} [CommRing R] [IsReduced R]
    [Algebra c.F R] (y : FrPt Xo c R) :
    ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (φ : R →ₐ[c.F] Ω) (z : FrPt Xo c Ω),
      FrMap φ y z → φ v = ∑ᶠ C, term P p i f z C := by
  obtain ⟨⟨Z, -⟩, -⟩ := heckeInFamilies E H Dw l Xo P p i hr hA
  obtain ⟨B, _, _, h, hfin, het, hh, -, hu⟩ := GlobalTheory.T.exists_finiteEtale_algebra_pullback_affine _ _ Z.π₁ Z.fin₁ Z.et₁ R y.x
  letI : Algebra c.F B := ((algebraMap R B).comp (algebraMap c.F R)).toAlgebra
  haveI : IsScalarTower c.F R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hred : IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R B
  obtain ⟨yB, hyB⟩ := bc_exists (IsScalarTower.toAlgHom c.F R B) y
  obtain ⟨b, hb⟩ := exists_term hA hT Z hf yB h (hh.trans hyB.1.symm)
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_trace_eq_finsum_geometric_points_etale R B hfin het b
  refine ⟨v, fun Ω _ _ _ φ z hz => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels E H Dw l Xo P p i Z.toKerScheme hA Ω z.x
  let k : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ.toRingHom} → {w : Sp Ω ⟶ Z.Hk // w ≫ Z.π₁ = z.x} := fun χ =>
    ⟨spMap χ.1 ≫ h, by rw [Category.assoc, hh, ← Category.assoc, ChgBC.spMap_comp_ring, χ.2, hz.1]⟩
  have hk : Function.Bijective k := by
    rw [Function.bijective_iff_existsUnique]
    intro w
    obtain ⟨χ, ⟨h₁, h₂⟩, h₃⟩ := hu Ω φ.toRingHom w.1 (w.2.trans hz.1)
    exact ⟨⟨χ, h₁⟩, Subtype.ext h₂, fun χ' h' => Subtype.ext (h₃ _ ⟨χ'.2, congrArg Subtype.val h'⟩)⟩
  refine (hv Ω φ.toRingHom).trans (finsum_eq_of_bijective (e ∘ k) (e.bijective.comp hk) fun χ => ?_)
  let χ' : B →ₐ[c.F] Ω := { χ.1 with commutes' := fun r => (RingHom.congr_fun χ.2 _).trans (φ.commutes r) }
  have hm : FrMap χ' yB z := by
    obtain ⟨w, hw⟩ := bc_exists χ' yB
    have := frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ' y yB w hyB hw
    rw [show χ'.comp (IsScalarTower.toAlgHom c.F R B) = φ from AlgHom.ext (RingHom.congr_fun χ.2)] at this
    rwa [bc_unique hz this]
  exact hb Ω χ' z _ hm ((he (k χ) _).2 rfl)

theorem secTransform (hL : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.SecTransform := by
  intro E _ _ _ H Dw l Xo c P p i cq a n hr hs _ _ f hf
  have hA : admitted l P p := ⟨hs.max, hs.split, hs.prime, hs.under, hs.off⟩
  have hP := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hA
  have hT := hL.2.1 E H Dw l Xo c P p i hP
  have red : ∀ q : TRing c.F, IsReduced q.R := fun q => (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  choose g hg using fun (q : TRing c.F) (y : FrPt Xo c q.R) => haveI := red q; exists_sum hr hA hT hf y
  have ext : ∀ (q : TRing c.F) (v w : q.R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
      (φ : q.R →ₐ[c.F] Ω), φ v = φ w) → v = w := fun q v w h =>
    haveI := red q
    sub_eq_zero.1 (GeometricValues.eq_zero_of_forall_algClosed (K := c.F) _ fun Ω _ _ _ φ => by
      rw [map_sub, h Ω φ, sub_self])
  have hsec : g ∈ sec Xo c a n := by
    refine ⟨fun q q' φ y z h => ext _ _ _ fun Ω _ _ _ ψ => ?_, fun q t y y' h => ext _ _ _ fun Ω _ _ _ ψ => ?_⟩
    · obtain ⟨w, hw⟩ := bc_exists ψ z
      exact (hg q' z Ω ψ w hw).trans
        (hg q y Ω (ψ.comp φ) w (frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h hw)).symm
    · obtain ⟨w, hw⟩ := bc_exists ψ y
      obtain ⟨w', hw'⟩ := bc_exists ψ y'
      rw [map_mul, hg q y Ω ψ w hw, hg q y' Ω ψ w' hw']
      refine (GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame E H Dw l Xo c P p i a n hA hT (hL.2.2.1 E H Dw l Xo c P p i hP) f hf Ω _ w w'
        (frBorBC (Xo := Xo) (c := c) _ _ ψ t y y' w w' h hw hw')).trans ?_
      congr 1
      simp [wchar]
  refine ⟨hkScal c cq P i n • g, Submodule.smul_mem _ _ hsec, fun Ω _ _ _ y => ?_⟩
  rw [evalAt_smul]
  congr 1
  have hy := GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c Ω y
  rw [evalAt, dif_pos hy]
  exact hg _ _ Ω _ y hy.choose_spec.choose_spec.choose_spec

end Sec

section Cusp

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open GlobalTheory.HkFam (admitted)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem perFr_natCast_smul (X : Data E r) (x : Frame X.Ψ r) (N : ℕ) (v : Fin r → E) (τ : E →+* ℂ) (m : ℕ) :
    Formalism.L2.PjFree.perFr X x ((N : E) • v) τ m = N * Formalism.L2.PjFree.perFr X x v τ m := by
  have e : ∀ τ : E →+* ℂ, Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  split_ifs
  · rw [e, Matrix.mulVec_smul]; rfl
  · simp
  · rw [e, FD.hermC_smul_right]; simp
  · simp
  · simp

theorem exists_qmatch (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) (hA : admitted l P p)
    {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom} {C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)}
    {z : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hC : Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C)
    (hm : HkPtC p (U.un k x) C z) (hb : FrBor t (U.un k' x') z)
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : QMatch (U.X k) (U.X k') p a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t (some j) : CAt σ) = 1 := by
  have hp0 : 0 < p := hA.2.2.1.pos
  obtain ⟨gam, A, htr, hsur, hA0, hAp, hAt⟩ := GlobalTheory.T.exists_similitude_triangular_periods_of_heckePoint E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_similitude_sq E r (U.X k) (U.X k') p hp0 (hxi k k') gam htr hsur
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hAp (e.symm τ) i hi ⟨v, hv⟩
      rw [he, ← hav, perFr_natCast_smul] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hp0.ne') this
  rcases hε with rfl | rfl
  · have h : QMatch (U.X k) (U.X k') p a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul],
        fun v hv => hav ⟨v, hv⟩ ▸ (gam ⟨v, hv⟩).2, hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := GlobalTheory.T.frames_differ_by_isometry_of_triangular_periods E r _ _ p a h hp0 (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun ⟨τ, i⟩ => ?_⟩
    have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
    rw [e.symm_apply_apply, hAt] at this
    exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_qmatch {k k' : U.Comp} {N : ℕ} {a : GL (Fin r) E} (h : QMatch (U.X k) (U.X k') N a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) (hA : admitted l P p) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hD : Dom w n) {cq : c.F} {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsTransform Xo c P p i cq n f g) (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨M, hM⟩ := exists_card_heckeKer_le (Xo := Xo) (i := i) hA
  refine GlobalTheory.T.mem_cuspSections_of_dominated_rational_isometries E r _ U.Comp U.X _ _ _ _ p (‖σ (hkScal c cq P i n)‖ * (M * ((Ideal.absNorm P : ℝ) ^ i) ^ n))
    hA.2.2.1.pos (by positivity) hsec hfc (fun j a h => laU_qmatch h w n) fun x hx B hB0 hB => ?_
  obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  have hb0 := norm_pos_iff.2 (AR.Up.OntoE.bchar_ne _ (Formalism.L2.PjFree.laU U w n k) hb₀)
  have hterm : ∀ C, cabs (term P p i f (U.un k x₀) C) ≤
      ((Ideal.absNorm P : ℝ) ^ i) ^ n * (‖bchar (Formalism.L2.PjFree.laU U w n k) b₀‖ * B) := fun C => by
    rw [term, hkTerm]
    split_ifs with hex
    swap
    · exact (norm_zero (E := ℂ)).trans_le (by positivity)
    have hz := hex.choose_spec
    generalize hex.choose = z at hz ⊢
    obtain ⟨k', x', t, hx', hb⟩ := hun2 z
    obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_qmatch hσ hU hr hxi hA C.2 hz hb hx₀ hx'
    have ht0 := GlobalTheory.T.heckeIsogeny_generatorRatio_le_traceTerms E H Dw l Xo c σ r U hσ hU P p i k k' x₀ x' C.1 z t hA C.2 hz hb hx₀ hx'
    have hQ := (hfc k').1.1
    have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
      (inferInstanceAs (IsReduced ℂ)) w n f hf t _ z hb
    have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ ≤ ((Ideal.absNorm P : ℝ) ^ i) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
        ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
      rw [this, norm_prod, Fintype.prod_option, Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ = 1 from ht j, one_pow], _root_.mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ht0 n
    have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
      unfold bchar
      simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
    have v5 : ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ ≤ ‖bchar (Formalism.L2.PjFree.laU U w n k) b₀‖ * B := by
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, _root_.one_mul, e₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_qmatch h w n), norm_mul]
      exact mul_le_mul_of_nonneg_left (hB k' a h) hb0.le
    rw [v2] at v5
    refine (congrArg cabs v3).trans_le ((norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans_le ?_)
    exact mul_le_mul v4 v5 (norm_nonneg _) (by positivity)
  have hfin := hF (CAt σ) (U.un k x₀)
  have := Fintype.ofFinite (hkKer (Xo := Xo) P p i (CAt σ) (U.un k x₀))
  have hc : (Fintype.card (hkKer (Xo := Xo) P p i (CAt σ) (U.un k x₀)) : ℝ) ≤ M := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hM (CAt σ) (U.un k x₀).x
  have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 =
      σ (hkScal c cq P i n) * ∑ C, Formalism.L2.PjFree.toC (term P p i f (U.un k x₀) C) :=
    (dif_pos x₀.2).trans ((hT (CAt σ) (U.un k x₀)).trans (congrArg _ (finsum_eq_sum_of_fintype _)))
  have v7 := congrArg norm v1
  rw [e₀, hsec.2.1 x hx b₀ hb₀, norm_mul, norm_mul] at v7
  have v8 := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul Finset.univ
    (fun C => ‖Formalism.L2.PjFree.toC (term P p i f (U.un k x₀) C)‖) _ fun C _ => hterm C)
  rw [Finset.card_univ, nsmul_eq_mul] at v8
  refine le_of_mul_le_mul_left ?_ hb0
  rw [v7]
  refine (mul_le_mul_of_nonneg_left (v8.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
    (norm_nonneg _)).trans_eq (by ring)

end Cusp

open Formalism.BasicNotions Formalism.L2.Pj in

theorem cuspTransform : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.CuspTransform := by
  intro D T h j hj P p i cq a n hs _ hD hE hDt hF f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  obtain ⟨hs', hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  refine (mem_cusp _ _ _ _ _ _).2 ⟨(hkOp hE hDt hF f).2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  exact rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm)
    ⟨hs.max, hs.split, hs.prime, hs.under, hs.off⟩ hD hs' (hkOp hE hDt hF f).2
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) hF (hkOp_spec hE hDt hF f) k

theorem heckeTransform_of_pointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform :=
  fun h => ⟨secTransform h, cuspTransform⟩

end GlobalTheory.HeckeEx
