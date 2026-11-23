import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusMono

open AddMonoidAlgebra (single)
open GlobalTheory.TorusUnit GlobalTheory.BiextTriv

theorem eq_single_of_isUnit_coeff {A X : Type} [CommRing A] [IsReduced A] [AddCommGroup X]
    [TwoUniqueSums X] {u : AddMonoidAlgebra A X} (hu : IsUnit u) {χ : X}
    (hχ : IsUnit (u.coeff χ)) : u = single χ (u.coeff χ) := by
  classical
  have key : ∀ z, z ≠ χ → u.coeff z = 0 := by
    intro z hz
    have hn : u.coeff z ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Ideal.mem_sInf.2 fun {p} hp => ?_
      have : p.IsPrime := hp
      obtain ⟨a, c, -, e⟩ := Semi.Rosenlicht.isUnit_eq_single
        (hu.map (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk p)))
      have ec : ∀ w, Ideal.Quotient.mk p (u.coeff w) = (single a c : AddMonoidAlgebra (A ⧸ p) X).coeff w := by
        intro w
        rw [← e, AddMonoidAlgebra.coeff_mapRingHom]
      have ha : a = χ := by
        by_contra hne
        have h1 := ec χ
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne] at h1
        exact (hχ.map (Ideal.Quotient.mk p)).ne_zero h1
      have h2 := ec z
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (ha.trans_ne hz.symm)] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    rw [nilradical_eq_zero] at hn
    exact hn
  ext z
  by_cases h : z = χ
  · subst h; simp
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, key z h, Ne.symm h]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def IsMonoNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ ∃ c : R, IsUnit c ∧ (expand y).hom ρ = single χ c

theorem IsMonoNear.residueField {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) : ∃ c : Y.left.residueField p, c ≠ 0 ∧
      (expand (Y.left.fromSpecResidueField p)).hom ρ = single χ c := by
  obtain ⟨R, y, hy, hp, c, hc, he⟩ := h
  have H : Set.range (Y.left.fromSpecResidueField p) ⊆ Set.range y := by
    rw [Scheme.range_fromSpecResidueField]; simpa using hp
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f ≫ y = Y.left.fromSpecResidueField p :=
    ⟨Spec.preimage (IsOpenImmersion.lift y _ H), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  refine ⟨f.hom c, (hc.map _).ne_zero, ?_⟩
  rw [← hf, expand_map, he]
  simp

theorem IsMonoNear.unique {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) (h' : IsMonoNear ρ χ' p) : χ = χ' := by
  classical
  obtain ⟨c, hc, e⟩ := h.residueField
  obtain ⟨c', -, e'⟩ := h'.residueField
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f χ) (e.symm.trans e')
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  exact hc this

theorem exists_isMonoNear [Module.Free ℤ X] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) (p : Y.left) : ∃ χ, IsMonoNear ρ.val χ p := by
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (ρ.isUnit.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ.val).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  have hopen : IsOpenImmersion (Spec.map g ≫ y) := inferInstance
  have hred : IsReduced (Spec (CommRingCat.of (Localization.Away a))) :=
    isReduced_of_isOpenImmersion (Spec.map g ≫ y)
  have hred' : _root_.IsReduced (Localization.Away a) :=
    (affine_isReduced_iff (CommRingCat.of (Localization.Away a))).1 hred
  have hcoeff : ((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ = algebraMap R (Localization.Away a) a := by
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hunit : IsUnit (((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ) := by
    rw [hcoeff]
    exact IsLocalization.Away.algebraMap_isUnit a
  refine ⟨χ, _, Spec.map g ≫ y, hopen, ?_, _, hunit,
    eq_single_of_isUnit_coeff (ρ.isUnit.map (expand _).hom) hunit⟩
  have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
    rw [this]; exact hχ
  refine ⟨r, ?_⟩
  rw [← hq, ← hr]
  exact Scheme.Hom.comp_apply _ _ _

theorem snd_expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    (snd (splitTorus S X) Y).left.appTop ≫ expand y =
      y.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ const X R := by
  rw [expand, value, ← Scheme.Hom.comp_appTop_assoc, prodPoint_snd, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]

theorem eq_char_mul [Module.Free ℤ X] [ConnectedSpace Y.left] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) :
    ∃ χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val *
      (snd (splitTorus S X) Y).left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) := by
  choose c hc using exists_isMonoNear (X := X) (Y := Y) ρ
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_⟩
  obtain ⟨R, y, hy, hp, d, -, he⟩ := hc p
  refine ⟨R, y, hy, hp, ?_⟩
  have e1 := congrArg (fun f => f.hom ρ.val) (expand_aug (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  rw [he, aug_single] at e1
  have e2 := congrArg (fun f => f.hom ((unitSec X Y).appTop.hom ρ.val)) (snd_expand (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [map_mul, e2, ← e1, expand_char, he, hlc.apply_eq_of_preconnectedSpace p p₀]
  simp [const, AddMonoidAlgebra.single_mul_single]

end GlobalTheory.CompanionTheory.TorusMono

open GlobalTheory.CompanionTheory.TorusMono GlobalTheory.BiextTriv in

theorem GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S) [ConnectedSpace Y.left] [IsReduced Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ), ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift t y).left.appTop.hom ρ.val = (chV t χ).val * (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
  intro S X _ _ Y _ _ ρ
  obtain ⟨χ, hχ⟩ := eq_char_mul ρ
  refine ⟨χ, fun Z t y => ?_⟩
  have c1 : ∀ v, (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom v) =
      t.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (fst (splitTorus S X) Y).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c2 : ∀ v, (lift t y).left.appTop.hom ((snd (splitTorus S X) Y).left.appTop.hom v) =
      y.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (snd (splitTorus S X) Y).left = y.left := by
      rw [← Over.comp_left, lift_snd]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c3 : y.left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) =
      (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
    rw [← comp_unitSec, Scheme.Hom.comp_appTop]
    rfl
  conv_lhs => rw [hχ]
  rw [map_mul, c1, c2, c3, chV_val]
