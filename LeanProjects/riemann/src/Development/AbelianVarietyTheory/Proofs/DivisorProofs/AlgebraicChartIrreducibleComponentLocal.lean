import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.HorComp

namespace GlobalTheory.HorComp.OneComp

section

open Limits

theorem isDomain_stalk_pullback {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k) (τ : k →+* ℂ)
    (U : Y.Opens) [Smooth (U.ι ≫ q)] (x : (pullback q (spMap τ) : Scheme.{0}))
    (hx : pullback.fst q (spMap τ) x ∈ U) : IsDomain ((pullback q (spMap τ)).presheaf.stalk x) := by
  have h := (isPullback_morphismRestrict (pullback.fst q (spMap τ)) U).paste_vert
    (IsPullback.of_hasPullback q (spMap τ))
  have hs : Smooth ((pullback.fst q (spMap τ) ⁻¹ᵁ U).ι ≫ pullback.snd q (spMap τ)) :=
    MorphismProperty.of_isPullback h ‹_›
  have hd := (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
    ((pullback.fst q (spMap τ) ⁻¹ᵁ U).ι ≫ pullback.snd q (spMap τ)) (fun y => by
      have hf : IsField ((Sp ℂ).presheaf.stalk y) := by
        letI := (Sp ℂ).presheaf.algebra_section_stalk (⟨y, trivial⟩ : (⊤ : (Sp ℂ).Opens))
        have := (isAffineOpen_top (Sp ℂ)).isLocalization_stalk ⟨y, trivial⟩
        have hF : IsField Γ(Sp ℂ, ⊤) :=
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField ℂ)
        letI := hF.toField
        exact (RingEquiv.ofBijective _ (IsField.localization_map_bijective
          (M := ((isAffineOpen_top (Sp ℂ)).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl)
          (Rₘ := (Sp ℂ).presheaf.stalk y) (fun h => h (Ideal.zero_mem _)) hF)).symm.toMulEquiv.isField hF
      letI := hf.toField
      exact ⟨inferInstance, inferInstance⟩) ⟨x, hx⟩).1
  exact ((pullback.fst q (spMap τ) ⁻¹ᵁ U).stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}

theorem isPullback_toGenCx (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) :
    IsPullback (toGenCx j hj σ) (pullback.fst _ _) (pullback.fst (genStr Z) (spMap σ) ≫ genι Z) j := by
  have h₁ := (IsPullback.of_hasPullback (genStr Z) (spMap σ)).paste_horiz
    (IsPullback.of_hasPullback Z.s (spMap β))
  refine IsPullback.of_right ?_ ?_ h₁.flip
  · have e : toGenCx j hj σ ≫ pullback.snd (genStr Z) (spMap σ) = pullback.snd _ _ := pullback.lift_snd _ _ _
    rw [e, hj, spMap_comp_spMap]
    exact (IsPullback.of_hasPullback _ _).flip
  · have e : toGenCx j hj σ ≫ pullback.fst (genStr Z) (spMap σ) = toGen j hj σ := pullback.lift_fst _ _ _
    rw [← Category.assoc, e]
    exact pullback.lift_fst _ _ _

noncomputable def fibPt (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) : Sp ℂ ⟶ cxFib β q σ :=
  pullback.lift y.1 (𝟙 _) (y.2.trans (Category.id_comp _).symm)

theorem ptOf_up_eq (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    ptOf Z (up j hj σ y) = toGenCx j hj σ (fibPt σ y (IsLocalRing.closedPoint ℂ)) := by
  have e : (pullback.lift (up j hj σ y).1 (𝟙 _) ((up j hj σ y).2.trans (Category.id_comp _).symm) :
      Sp ℂ ⟶ genCx Z σ) = fibPt σ y ≫ toGenCx j hj σ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp only [fibPt, toGenCx, toGen, up, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.id_comp]
    · have e : toGenCx j hj σ ≫ pullback.snd (genStr Z) (spMap σ) = pullback.snd _ _ := pullback.lift_snd _ _ _
      rw [Category.assoc, e]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  exact congrArg (fun g : Sp ℂ ⟶ genCx Z σ => g (IsLocalRing.closedPoint ℂ)) e

theorem component_eq_of_chart (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) {n : ℕ}
    (ch : AlgChart q (σ.comp β) n) {y : CxPts q (σ.comp β)} (hy : y ∈ ch.e.source)
    {C C' : Set (cxFib β q σ)} (hC : C ∈ irreducibleComponents (cxFib β q σ))
    (hC' : C' ∈ irreducibleComponents (cxFib β q σ))
    (h : up j hj σ y ∈ ptsOf Z (toGenCx j hj σ '' C)) (h' : up j hj σ y ∈ ptsOf Z (toGenCx j hj σ '' C')) :
    C = C' := by
  have hci : IsClosedImmersion (toGenCx j hj σ) :=
    MorphismProperty.of_isPullback (isPullback_toGenCx j hj σ).flip ‹_›
  have hinj : Function.Injective (toGenCx j hj σ) := (toGenCx j hj σ).isClosedEmbedding.injective
  simp only [ptsOf, Set.mem_setOf_eq, ptOf_up_eq, hinj.mem_set_image] at h h'
  have hsm := ChartSmooth.smooth_chart _ _ q _ n ch
  have hs : Smooth (ch.U.ι ≫ q) := SmoothOfRelativeDimension.smooth n _
  have e : pullback.fst q (spMap (σ.comp β)) (fibPt σ y (IsLocalRing.closedPoint ℂ)) =
      y.1 (IsLocalRing.closedPoint ℂ) :=
    congrArg (fun g : Sp ℂ ⟶ Y => g (IsLocalRing.closedPoint ℂ)) (pullback.lift_fst _ _ _)
  have hd := isDomain_stalk_pullback q (σ.comp β) ch.U (fibPt σ y (IsLocalRing.closedPoint ℂ))
    (e ▸ mem_ptsIn.1 (ch.source_subset hy))
  exact IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hC hC' h h'

end

theorem component_unique : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → ∀ C ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), ∀ C' ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' C) → up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' C') → C = C' := by
  intro D A N j S κ s σ Y _ q jm _ hq n _ ch y hy C hC C' hC' h h'
  exact component_eq_of_chart jm hq σ ch hy hC hC' h h'

end GlobalTheory.HorComp.OneComp
