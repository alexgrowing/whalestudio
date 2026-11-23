import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AutomorphicArithmetic.KaehlerVanishing.DerivationEqOfFormallyEtaleOfEvaluationEq
import Development.AutomorphicArithmetic.KaehlerVanishing.KaehlerFunctionalVanishingOfLocalizationAtPrime

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

namespace UpperTheory.Gal.productCup_of_system

private theorem exists_stalk {Y : Scheme.{0}} (s' : Y ⟶ Sp ℂ) (y : CxPts s' (RingHom.id ℂ)) :
    ∃ (_ : Algebra ℂ (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))))
      (ev : (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) →ₐ[ℂ] ℂ),
      (∀ (W : Y.Opens) (h : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (c : ℂ),
        (Y.presheaf.germ W _ h).hom (algebraMap ℂ (Sec s' W) c) = algebraMap ℂ _ c) ∧
      (∀ (W : Y.Opens) (h : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (b : Γ(Y, W)),
        ev ((Y.presheaf.germ W _ h).hom b) = CxPts.ev s' (RingHom.id ℂ) W b y) := by
  have bridge : ∀ (W : Y.Opens) (hW : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (b : Γ(Y, W)),
      (Scheme.stalkClosedPointTo y.1).hom ((Y.presheaf.germ W _ hW).hom b) = valR y.1 W b := by
    intro W hW b
    have hh : ⊤ ≤ y.1 ⁻¹ᵁ W := (Points.le_preimage_iff y.1 W).mpr hW
    rw [valR, dif_pos hh]
    have := congrArg (fun g => g.hom b) (Scheme.germ_stalkClosedPointTo y.1 W hW)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp [Scheme.Hom.appLE]
    rfl
  have glue : ∀ (W : Y.Opens) (hW : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (c : ℂ),
      (Y.presheaf.germ W _ hW).hom (algebraMap ℂ (Sec s' W) c) =
        (Y.presheaf.germ ⊤ _ trivial).hom ((secMap s' ⊤).hom c) := by
    intro W hW c
    show (Y.presheaf.germ W _ hW).hom ((s'.appLE ⊤ W _).hom _) =
      (Y.presheaf.germ ⊤ _ trivial).hom ((s'.appLE ⊤ ⊤ _).hom _)
    rw [← Scheme.Hom.appLE_map (i := (homOfLE le_top).op), CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
    exact le_top
  letI alg : Algebra ℂ (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    ((Y.presheaf.germ ⊤ _ trivial).hom.comp (secMap s' ⊤).hom).toAlgebra
  have hev : ∀ c : ℂ, (Scheme.stalkClosedPointTo y.1).hom (algebraMap ℂ _ c) = c := by
    intro c
    have htop : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : Y.Opens) := Points.le_preimage_top y.1
    exact (bridge ⊤ trivial _).trans (Points.valR_constFn_of_over s' (RingHom.id ℂ) y.1 y.2 ⊤ htop c)
  refine ⟨alg, { toRingHom := (Scheme.stalkClosedPointTo y.1).hom, commutes' := hev }, ?_, ?_⟩
  · intro W hW c
    exact glue W hW c
  · intro W hW b
    exact bridge W hW b

end UpperTheory.Gal.productCup_of_system

namespace UpperTheory.Gal.productCup_of_system

private theorem mem_max_iff {S : Type} [CommRing S] [IsLocalRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (a : S) :
    a ∈ IsLocalRing.maximalIdeal S ↔ ev a = 0 := by
  have hs : Function.Surjective ev := fun c => ⟨algebraMap ℂ S c, by simp⟩
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ev hs), RingHom.mem_ker]

private theorem exists_der {Y : Scheme.{0}} (s' : Y ⟶ Sp ℂ) (y0 : Y)
    [Algebra ℂ (Y.presheaf.stalk y0)] (ev : (Y.presheaf.stalk y0) →ₐ[ℂ] ℂ)
    (V : Y.Opens) (hV : IsAffineOpen V) (h : y0 ∈ V)
    (halg : ∀ c : ℂ, (Y.presheaf.germ V y0 h).hom (algebraMap ℂ (Sec s' V) c) = algebraMap ℂ _ c)
    (d : ℕ) (φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)) (e : Sec s' V → ℂ)
    (he : ∀ b : Sec s' V, e b = ev ((Y.presheaf.germ V y0 h).hom b))
    (hs : ∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = e b • φ ω)
    (hk : ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
      (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i) :
    ∃ δ : (Y.presheaf.stalk y0) →ₗ[ℂ] (Fin d → ℂ),
      (∀ a b, δ (a * b) = ev a • δ b + ev b • δ a) ∧
      (∀ b : Sec s' V, δ ((Y.presheaf.germ V y0 h).hom b) = φ (KaehlerDifferential.D ℂ (Sec s' V) b)) ∧
      ∀ η : (Y.presheaf.stalk y0) →ₗ[ℂ] ℂ, (∀ a b, η (a * b) = ev a * η b + ev b * η a) →
        ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a) := by
  letI : Algebra (Sec s' V) (Y.presheaf.stalk y0) := (Y.presheaf.germ V y0 h).hom.toAlgebra
  haveI : IsScalarTower ℂ (Sec s' V) (Y.presheaf.stalk y0) :=
    IsScalarTower.of_algebraMap_eq (fun c => (halg c).symm)
  let p : Ideal (Sec s' V) := (hV.primeIdealOf ⟨y0, h⟩).asIdeal
  haveI : p.IsPrime := (hV.primeIdealOf ⟨y0, h⟩).isPrime
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y0) p := hV.isLocalization_stalk ⟨y0, h⟩
  have hp : ∀ b : Sec s' V, b ∈ p ↔ ev (algebraMap (Sec s' V) _ b) = 0 := by
    intro b
    rw [← mem_max_iff ev, ← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y0) p]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := UpperTheory.kaehler_functional_vanishing_of_localization_at_prime (B := Sec s' V) (S := Y.presheaf.stalk y0) p ev hp d φ
    (fun b ω => (hs b ω).trans (by rw [he]; rfl))
    (fun ω hω => by
      obtain ⟨m, b, ω', hb, hω⟩ := hk ω hω
      exact ⟨m, b, ω', fun i => (he (b i)).symm.trans (hb i), hω⟩)
  exact ⟨δ, h1, h2, h3⟩

private noncomputable def pb {Z Y : Scheme.{0}} (c : Y ⟶ Z) (U : Z.Opens) (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) :
    Γ(Z, U) →+* Y.presheaf.stalk y0 :=
  (Y.presheaf.germ (c ⁻¹ᵁ U) y0 h).hom.comp (c.app U).hom

private theorem pb_res {Z Y : Scheme.{0}} (c : Y ⟶ Z) {U U0 : Z.Opens} (e0 : U0 ≤ U) {W : Y.Opens}
    (e : W ≤ c ⁻¹ᵁ U) (y0 : Y) (hW : y0 ∈ W) (h : y0 ∈ c ⁻¹ᵁ U0) (f : Γ(Z, U)) :
    pb c U0 y0 h ((Z.presheaf.map (homOfLE e0).op).hom f) =
      (Y.presheaf.germ W y0 hW).hom ((c.appLE U W e).hom f) := by
  simp [pb, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

private theorem pb_const {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (c : Y ⟶ Z) (hc : c ≫ s = s')
    (U : Z.Opens) (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) [Algebra ℂ (Y.presheaf.stalk y0)]
    (halg : ∀ (W : Y.Opens) (h : y0 ∈ W) (r : ℂ),
      (Y.presheaf.germ W y0 h).hom (algebraMap ℂ (Sec s' W) r) = algebraMap ℂ _ r) (r : ℂ) :
    pb c U y0 h (algebraMap ℂ (Sec s U) r) = algebraMap ℂ _ r := by
  have key := semiHom_appSec hc U
  unfold SemiHom at key
  have e1 : appSec s s' c U (algebraMap ℂ (Sec s U) r) = algebraMap ℂ (Sec s' (c ⁻¹ᵁ U)) r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, key r 1, map_one]
    rfl
  rw [← halg _ h r, ← e1]
  rfl

private theorem pb_etale {Z Y : Scheme.{0}} (c : Y ⟶ Z) (hc : Etale c) (U : Z.Opens) (hU : IsAffineOpen U)
    (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) : (pb c U y0 h).FormallyEtale := by
  obtain ⟨V, hVa, hV, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens h
  have eq : pb c U y0 h = (Y.presheaf.germ V y0 hV).hom.comp (c.appLE U V e).hom := by
    ext f
    simp [pb, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  rw [eq]
  apply RingHom.FormallyEtale.comp
  · have := HasRingHomProperty.appLE @Etale c hc ⟨U, hU⟩ ⟨V, hVa⟩ e
    exact this.formallyEtale
  · letI := (Y.presheaf.germ V y0 hV).hom.toAlgebra
    haveI := (show IsAffineOpen V from hVa).isLocalization_stalk ⟨y0, hV⟩
    exact Algebra.FormallyEtale.of_isLocalization ((show IsAffineOpen V from hVa).primeIdealOf ⟨y0, hV⟩).asIdeal.primeCompl

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.tanConj_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (y : CxPts s' (RingHom.id ℂ)), Etale c1 → y.1 ≫ c1 = y.1 ≫ c2 → ∀ A A' : Matrix (Fin d) (Fin d) ℂ, IsTan d c1 c2 h1 h2 y A → IsTan d c1 c2 h1 h2 y A' → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ A' = P * A * P⁻¹ := by
  intro Z Y s s' d c1 c2 h1 h2 y hc hcc A A' hA hA'
  obtain ⟨inst, ev, halg, hev⟩ := exists_stalk s' y
  obtain ⟨U, V, hV1, hV2, t, hyV, hU, hV, φ, hφs, hφ1, hφ2, hφk⟩ := hA
  obtain ⟨U', V', hV1', hV2', t', hyV', hU', hV', φ', hφs', hφ1', hφ2', hφk'⟩ := hA'
  have hy0V : y.1 (IsLocalRing.closedPoint ℂ) ∈ V := CxPts.mem_ptsIn.mp hyV
  have hy0V' : y.1 (IsLocalRing.closedPoint ℂ) ∈ V' := CxPts.mem_ptsIn.mp hyV'
  have hmU : c1 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U ⊓ U' := ⟨hV1 hy0V, hV1' hy0V'⟩
  obtain ⟨U0, hU0a, hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hmU
  have h1' : y.1 (IsLocalRing.closedPoint ℂ) ∈ c1 ⁻¹ᵁ U0 := hmem
  have hpt : c2 (y.1 (IsLocalRing.closedPoint ℂ)) = c1 (y.1 (IsLocalRing.closedPoint ℂ)) := by
    have := congrArg (fun g : Sp ℂ ⟶ Z => g (IsLocalRing.closedPoint ℂ)) hcc
    exact this.symm
  have h2' : y.1 (IsLocalRing.closedPoint ℂ) ∈ c2 ⁻¹ᵁ U0 := by
    show c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U0
    rw [hpt]
    exact hmem
  letI : Algebra (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    (pb c1 U0 _ h1').toAlgebra
  haveI : Algebra.FormallyEtale (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    pb_etale c1 hc U0 hU0a _ h1'
  haveI : IsScalarTower ℂ (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    IsScalarTower.of_algebraMap_eq (fun r => (pb_const c1 h1 U0 _ h1' halg r).symm)
  let a2 : Sec s U0 →ₐ[ℂ] Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ)) :=
    { toRingHom := pb c2 U0 _ h2', commutes' := pb_const c2 h2 U0 _ h2' halg }
  have hval : ∀ f : Sec s U0, ev (algebraMap (Sec s U0) _ f) = ev (a2 f) := by
    intro f
    have e1 : ev (pb c1 U0 _ h1' f) = valR (y.1 ≫ c1) U0 f :=
      (hev _ h1' _).trans (Points.valR_comp y.1 c1 U0 f).symm
    have e2 : ev (pb c2 U0 _ h2' f) = valR (y.1 ≫ c2) U0 f :=
      (hev _ h2' _).trans (Points.valR_comp y.1 c2 U0 f).symm
    show ev (pb c1 U0 _ h1' f) = ev (pb c2 U0 _ h2' f)
    rw [e1, e2, hcc]
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_der s' _ ev V hV hy0V (halg V hy0V) d φ
    (fun b => CxPts.ev s' (RingHom.id ℂ) V b y) (fun b => (hev V hy0V b).symm) hφs hφk
  obtain ⟨δ', hδ1', hδ2', hδ3'⟩ := exists_der s' _ ev V' hV' hy0V' (halg V' hy0V') d φ'
    (fun b => CxPts.ev s' (RingHom.id ℂ) V' b y) (fun b => (hev V' hy0V' b).symm) hφs' hφk'
  have e0 : U0 ≤ U := hle.trans inf_le_left
  have e0' : U0 ≤ U' := hle.trans inf_le_right
  let τ : Fin d → Sec s U0 := fun l => (Z.presheaf.map (homOfLE e0).op).hom (t l)
  let τ' : Fin d → Sec s U0 := fun l => (Z.presheaf.map (homOfLE e0').op).hom (t' l)
  refine UpperTheory.derivation_eq_of_formallyEtale_of_evaluation_eq (A := Sec s U0) a2 ev hval d δ δ' hδ1 hδ1' hδ3 hδ3' τ τ' A A' ?_ ?_ ?_ ?_
  · intro l
    show δ (pb c1 U0 _ h1' (τ l)) = _
    rw [show pb c1 U0 _ h1' (τ l) = _ from pb_res c1 e0 hV1 _ hy0V h1' (t l)]
    exact (hδ2 _).trans (hφ1 l)
  · intro j
    show δ (pb c2 U0 _ h2' (τ j)) = _
    rw [show pb c2 U0 _ h2' (τ j) = _ from pb_res c2 e0 hV2 _ hy0V h2' (t j)]
    exact (hδ2 _).trans (hφ2 j)
  · intro l
    show δ' (pb c1 U0 _ h1' (τ' l)) = _
    rw [show pb c1 U0 _ h1' (τ' l) = _ from pb_res c1 e0' hV1' _ hy0V' h1' (t' l)]
    exact (hδ2' _).trans (hφ1' l)
  · intro j
    show δ' (pb c2 U0 _ h2' (τ' j)) = _
    rw [show pb c2 U0 _ h2' (τ' j) = _ from pb_res c2 e0' hV2' _ hy0V' h2' (t' j)]
    exact (hδ2' _).trans (hφ2' j)
