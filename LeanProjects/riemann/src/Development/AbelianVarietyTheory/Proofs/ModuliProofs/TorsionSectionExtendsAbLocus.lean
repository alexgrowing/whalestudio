import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_section_of_pow_eq_one {T V : Scheme.{0}} [IsLocallyNoetherian T] (hT : Geo.Tor.IsNormalScheme T)
    (j : V ⟶ T) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (G : Over T) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤)))
    (P : Over T) (x : P ⟶ G) (hx : x ^ n = 1) (k : V ⟶ P.left) (hk : k ≫ P.hom = j) :
    ∃ σ : T ⟶ G.left, σ ≫ G.hom = 𝟙 T ∧ j ≫ σ = k ≫ x.left := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA T G n hn
  have h₂ : IsProper ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : IsProper (Out.mulA G n).left := IsProper.of_comp _ G.hom
  have h₄ : LocallyQuasiFinite (Out.mulA G n).left := by
    refine ⟨fun {U} hU {W} hW e => ?_⟩
    have a₁ := (Out.mulA G n).left.formallyUnramified_appLE hU hW e
    have a₂ := (Out.mulA G n).left.finiteType_appLE hU hW e
    algebraize [((Out.mulA G n).left.appLE U W e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  have h₅ : IsFinite (Out.mulA G n).left := .of_isProper_of_locallyQuasiFinite _
  have e₁ : x ≫ Out.mulA G n = toUnit P ≫ η[G] := by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  have e₂ : x.left ≫ (Out.mulA G n).left = P.hom ≫ (η[G]).left := by
    rw [← Over.comp_left, e₁]; simp
  obtain ⟨σ, ⟨a, b⟩, -⟩ := existsUnique_lift_of_densePart T V G.left G.left j hT ‹_› ‹_› ‹_› ‹_›
    (Out.mulA G n).left (η[G]).left (k ≫ x.left) inferInstance
    (by rw [Category.assoc, e₂, ← hk, Category.assoc])
  refine ⟨σ, ?_, a⟩
  rw [← hw, reassoc_of% b]
  exact Over.w η[G]

theorem torsion_section_extends_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDedFrac β → AbOpen Y.t.G → ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (n : ℕ), IsUnit (n : O) → σ ^ n = 1 → Y.Extends U σ := by
  intro E _ _ _ H D l Xo c O _ β Y ⟨⟨_, hD⟩, _, hF⟩ ⟨U, hU, hP⟩
  refine ⟨U, hU, fun σ n hn hσ => ?_⟩
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have k₁ : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁
  have k₂ : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq j₂
  have k₄ : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄
  have k₃ : IsDominant j := by
    constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  have hT : Geo.Tor.IsNormalScheme U.toScheme := fun x => by
    obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have hn' : IsUnit (n : Γ(U.toScheme, ⊤)) := by
    simpa using hn.map ((U.ι ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  let G : Over U.toScheme := (Over.pullback U.ι).obj Y.t.G
  have hG : IsProper G.hom := by
    have : IsProper ((pullbackRestrictIsoRestrict Y.t.G.hom U).inv ≫ pullback.snd Y.t.G.hom U.ι) := hP
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  have gp := isGrpPullback_pullback Y.t.G U.ι
  have hc := Y.m.cart
  let ψ : Y.oF.t.G.left ⟶ G.left := gp.1.lift Y.m.φ (Y.oF.t.G.hom ≫ j)
    (by rw [Category.assoc, hj]; exact hc.1.w)
  have hψ : ψ ≫ pullback.fst Y.t.G.hom U.ι = Y.m.φ := gp.1.lift_fst _ _ _
  have gq : IsGrpPullback Y.oF.t.G G j ψ :=
    gp.cancel (by rw [hψ, hj]; exact hc) (gp.1.lift_snd _ _ _)
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT j G n hn' _ (pushHom gq _ σ)
    (by rw [← map_pow, hσ, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  refine ⟨s ≫ pullback.fst Y.t.G.hom U.ι, ?_, fun j' hj' => ?_⟩
  · rw [Category.assoc, gp.1.w, reassoc_of% hs₁]
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    rw [reassoc_of% hs₂, ← hψ]
    exact Category.assoc _ _ _

end GlobalTheory
