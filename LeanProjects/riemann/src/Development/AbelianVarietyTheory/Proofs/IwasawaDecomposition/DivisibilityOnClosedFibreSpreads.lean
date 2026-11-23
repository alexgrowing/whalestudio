import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Spread

theorem gs_fromSpecStalk (X : Scheme.{0}) (x : X) (U : X.Opens) (hx : x ∈ U) (c : Γ(X, U))
    (q : PrimeSpectrum (X.presheaf.stalk x)) :
    gs (X.fromSpecStalk x) q U c =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (gs (𝟙 X) x U c) := by
  have hq : X.fromSpecStalk x q ∈ U := by
    have : X.fromSpecStalk x q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
    exact this.mem_open U.2 hx
  rw [gs_eq _ _ _ hq, gs_eq _ _ _ hx]
  rw [Scheme.fromSpecStalk_app hx]
  simp only [CommRingCat.comp_apply, Scheme.ΓSpecIso_inv]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {V : Type} [CommRing V]

theorem stalkMap_cst {Y Z : Scheme.{0}} (g : Z ⟶ Y) (p : Y ⟶ Sp V) (z : Z) (v : V) :
    (g.stalkMap z).hom (cst p (g z) v) = cst (g ≫ p) z v := by
  have h : g z ∈ p ⁻¹ᵁ (⊤ : (Sp V).Opens) := trivial
  rw [cst, cst, ← gs_pull g p z ⊤ trivial, gs_stalkMap g z (p ⁻¹ᵁ ⊤) h, gs_pull (𝟙 Y) p (g z) ⊤ trivial,
    Category.id_comp]

theorem isUnit_cst_iff {Z : Scheme.{0}} (p : Z ⟶ Sp V) (z : Z) (v : V) :
    IsUnit (cst p z v) ↔ v ∉ (p z).asIdeal := by
  rw [cst, gs_stalkMap p z ⊤ trivial, isUnit_map_iff]
  let P : PrimeSpectrum V := p z
  have e : gs (𝟙 (Sp V)) (p z) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v) =
      algebraMap V ((Spec.structureSheaf V).presheaf.stalk P) v := by
    rw [gs_eq _ _ (⊤ : (Sp V).Opens) (show (𝟙 (Sp V) : Sp V ⟶ Sp V) (p z) ∈ (⊤ : (Sp V).Opens) from trivial)]
    rfl
  rw [e]
  exact IsLocalization.AtPrime.isUnit_to_map_iff ((Spec.structureSheaf V).presheaf.stalk P) P.asIdeal v

theorem isNormalScheme_sp (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Sp R) := by
  refine (isNormalScheme_iff _).2 fun P => ?_
  let P' : PrimeSpectrum R := P
  change IsDomain ((Spec.structureSheaf R).presheaf.stalk P') ∧
    IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk P')
  have hle := P'.asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors ((Spec.structureSheaf R).presheaf.stalk P') hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.Spread

namespace GlobalTheory.Spread

variable {V : Type} [CommRing V]

theorem cst_fromSpecStalk (X : Scheme.{0}) (x : X) (p : X ⟶ Sp V) (q : PrimeSpectrum (X.presheaf.stalk x))
    (v : V) :
    cst (X.fromSpecStalk x ≫ p) q v =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (cst p x v) := by
  unfold cst
  refine (gs_pull (X.fromSpecStalk x) p q ⊤ trivial _).symm.trans
    ((gs_fromSpecStalk X x (p ⁻¹ᵁ ⊤) trivial _ q).trans ?_)
  congr 1

theorem exists_closedFibre_of_generic (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R))
    [GrpObj G] [GeometricallyIntegral G.hom] (y : G.left)
    (hy : ∀ w : G.left, w ⤳ y → G.hom w = G.hom y → w = y) :
    ∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z := by
  set P := G.hom y
  have hI : IsIntegral (G.hom.fiber P) :=
    GeometricallyIntegral.geometrically_isIntegral (f := G.hom) ((Sp R).fromSpecResidueField P)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let η := G.hom.fiberι P (genericPoint (G.hom.fiber P))
  have hη : ∀ w : G.left, G.hom w = P → η ⤳ w := by
    intro w hw
    obtain ⟨w', rfl⟩ : w ∈ Set.range (G.hom.fiberι P) := by rw [Scheme.Hom.range_fiberι]; exact hw
    exact (genericPoint_specializes w').map (G.hom.fiberι P).continuous
  have hηP : G.hom η = P := by
    have : η ∈ Set.range (G.hom.fiberι P) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have hηy : η = y := hy η (hη y rfl) hηP
  let e := (MonObj.one : 𝟙_ (Over (Sp R)) ⟶ G).left
  have he : ∀ u, G.hom (e u) = u := fun u => by
    change (e ≫ G.hom) u = u
    rw [Over.w]
    rfl
  refine ⟨e (closedPoint R), he _, ?_⟩
  rw [← hηy]
  exact (hη (e P) (he P)).trans ((IsLocalRing.specializes_closedPoint P).map e.continuous)

end GlobalTheory.Spread

namespace GlobalTheory.Spread

theorem dvd_of_dvd_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (r : R), r ≠ 0 → ∀ (W : G.left.Opens) (a : Γ(G.left, W))
    (x : G.left), x ∈ W → (∀ y ∈ W, (∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z) → cst G.hom y r ∣ gs (𝟙 G.left) y W a) →
    cst G.hom x r ∣ gs (𝟙 G.left) x W a := by
  intro R _ _ _ hN hIC G _ hG r hr W a x hxW H
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom
  have : IsNormalScheme (Sp R) := isNormalScheme_sp R
  have : IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨_, _⟩ := (isNormalScheme_iff G.left).1 ‹_› x
  have ha : cst G.hom x r ≠ 0 := by
    intro h0
    have hreg := cst_regular G.hom x hr
    rw [h0] at hreg
    exact one_ne_zero (hreg (by simp : (0 : G.left.presheaf.stalk x) * 1 = 0 * 0))
  refine GlobalTheory.dvd_of_forall_height_eq_one ha fun q _ hq1 haq => ?_
  let f := G.left.fromSpecStalk x
  let Q : PrimeSpectrum (G.left.presheaf.stalk x) := ⟨q, inferInstance⟩
  have hmem : ∀ Q' : PrimeSpectrum (G.left.presheaf.stalk x),
      r ∈ (G.hom (f Q')).asIdeal ↔ cst G.hom x r ∈ Q'.asIdeal := by
    intro Q'
    letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q'
    have e1 := isUnit_cst_iff (f ≫ G.hom) Q' r
    rw [cst_fromSpecStalk] at e1
    have e2 := IsLocalization.AtPrime.isUnit_to_map_iff
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q') Q'.asIdeal (cst G.hom x r)
    have e := e1.symm.trans e2
    constructor
    · intro h
      by_contra h'
      exact (e.2 h') h
    · intro h
      by_contra h'
      exact (e.1 h') h
  have hyx : f Q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨Q, rfl⟩
  have hyW : f Q ∈ W := hyx.mem_open W.2 hxW
  have key : ∃ z : G.left, G.hom z = closedPoint R ∧ f Q ⤳ z := by
    apply exists_closedFibre_of_generic R G (f Q)
    intro w hwy hw
    obtain ⟨Q'', rfl⟩ : w ∈ Set.range f := by
      rw [Scheme.range_fromSpecStalk]; exact hwy.trans hyx
    let Q' : PrimeSpectrum (G.left.presheaf.stalk x) := Q''
    have hsp : Q' ⤳ Q := (f.isEmbedding.isInducing.specializes_iff).1 hwy
    have hle : Q'.asIdeal ≤ q := (PrimeSpectrum.le_iff_specializes Q' Q).2 hsp
    have haQ' : cst G.hom x r ∈ Q'.asIdeal := (hmem Q').1 (by change r ∈ (G.hom (f Q'')).asIdeal; rw [hw]; exact (hmem Q).2 haq)
    have hQ : Q'' = Q := by
      by_contra hne
      have hlt : Q'.asIdeal < q := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have h1 := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      rw [h1] at haQ'
      exact ha haQ'
    rw [hQ]
  obtain ⟨t, ht⟩ := H (f Q) hyW key
  have hd := map_dvd (f.stalkMap Q).hom ⟨t, ht⟩
  replace hd : cst (f ≫ G.hom) Q r ∣ gs f Q W a := by
    have e1 := stalkMap_cst f G.hom Q r
    have e2 := gs_stalkMap f Q W hyW a
    rw [← e1, e2]
    exact hd
  rw [cst_fromSpecStalk, gs_fromSpecStalk _ x W hxW] at hd
  letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q
  haveI : IsLocalization Q.asIdeal.primeCompl
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q) :=
    StructureSheaf.IsLocalization.to_stalk _ Q
  obtain ⟨w, hw⟩ := hd
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := (Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
    Q.asIdeal.primeCompl w
  dsimp only at hw
  have e : algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (gs (𝟙 G.left) x W a * s) =
      algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (cst G.hom x r * c) := by
    rw [map_mul, hw]
    erw [mul_assoc, IsLocalization.mk'_spec]
    rw [map_mul]
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists Q.asIdeal.primeCompl _).1 e
  refine ⟨u * s, Q.asIdeal.primeCompl.mul_mem u.2 s.2, ⟨u * c, ?_⟩⟩
  linear_combination hu

end GlobalTheory.Spread
