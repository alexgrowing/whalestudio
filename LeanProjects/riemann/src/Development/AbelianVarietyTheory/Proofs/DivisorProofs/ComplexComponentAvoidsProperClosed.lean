import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFreeNeighbourhood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
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

noncomputable section

namespace GlobalTheory.HorComp

open CategoryTheory AlgebraicGeometry Limits

theorem exists_cxPt_component_notMem {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* ℂ)
    (hf : Function.Injective f) {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp R) [LocallyOfFiniteType q]
    (C : Set (pullback q (spMap f) : Scheme.{0})) (hC : C ∈ irreducibleComponents (pullback q (spMap f) : Scheme.{0}))
    (T : Set Y) (hT : IsClosed T) (hη : genericPoint Y ∉ T) :
    ∃ y : CxPts q f, GlobalTheory.IrrAn.pt q f y (IsLocalRing.closedPoint ℂ) ∈ C ∧ y.1 (IsLocalRing.closedPoint ℂ) ∉ T := by
  have hfl : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := f.toAlgebra
    have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hf
    have : Module.Flat R ℂ := inferInstance
    exact RingHom.flat_algebraMap_iff.2 this
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hξ : IsGenericPoint hC.1.genericPoint C := hC.1.isGenericPoint_genericPoint hCc
  obtain ⟨ξ', hξ', e⟩ := Flat.generalizingMap (pullback.fst q (spMap f))
    (genericPoint_specializes (pullback.fst q (spMap f) hC.1.genericPoint))
  have hξ'C : ξ' ∈ C := by
    have h : C ⊆ closure ({ξ'} : Set _) := by
      rw [← hξ.def]; exact specializes_iff_closure_subset.mp hξ'
    exact hC.2 isIrreducible_singleton.closure h (subset_closure rfl)
  have hO : IsOpen (pullback.fst q (spMap f) ⁻¹' Tᶜ) :=
    hT.isOpen_compl.preimage (pullback.fst q (spMap f)).continuous
  obtain ⟨y, hyC, hyT⟩ := GlobalTheory.IrrAn.ptsOf_nonempty R Y q f (C ∩ pullback.fst q (spMap f) ⁻¹' Tᶜ)
    (hCc.isLocallyClosed.inter hO.isLocallyClosed) ⟨ξ', hξ'C, by
      show pullback.fst q (spMap f) ξ' ∉ T
      rw [e]; exact hη⟩
  refine ⟨y, hyC, ?_⟩
  have e' : pullback.fst q (spMap f) (GlobalTheory.IrrAn.pt q f y (IsLocalRing.closedPoint ℂ)) =
      y.1 (IsLocalRing.closedPoint ℂ) :=
    congrArg (fun g : Sp ℂ ⟶ Y => g (IsLocalRing.closedPoint ℂ)) (pullback.lift_fst _ _ _)
  rw [← e']
  exact hyT

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}

theorem ptOf_up_eq_toGenCx_pt (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    ptOf Z (up j hj σ y) = toGenCx j hj σ (GlobalTheory.IrrAn.pt q (σ.comp β) y (IsLocalRing.closedPoint ℂ)) := by
  have e : (pullback.lift (up j hj σ y).1 (𝟙 _) ((up j hj σ y).2.trans (Category.id_comp _).symm) :
      Sp ℂ ⟶ genCx Z σ) = GlobalTheory.IrrAn.pt q (σ.comp β) y ≫ toGenCx j hj σ := by
    have a1 : toGenCx j hj σ ≫ pullback.fst _ _ = toGen j hj σ := pullback.lift_fst _ _ _
    have a2 : toGenCx j hj σ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have b1 : toGen j hj σ ≫ pullback.fst Z.s (spMap β) = pullback.fst _ _ ≫ j := pullback.lift_fst _ _ _
    have b2 : toGen j hj σ ≫ pullback.snd Z.s (spMap β) = pullback.snd _ _ ≫ spMap σ := pullback.lift_snd _ _ _
    have c1 : GlobalTheory.IrrAn.pt q (σ.comp β) y ≫ pullback.fst _ _ = y.1 := pullback.lift_fst _ _ _
    have c2 : GlobalTheory.IrrAn.pt q (σ.comp β) y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have d1 : (up j hj σ y).1 ≫ pullback.fst Z.s (spMap β) = y.1 ≫ j := pullback.lift_fst _ _ _
    have d2 : (up j hj σ y).1 ≫ pullback.snd Z.s (spMap β) = spMap σ := pullback.lift_snd _ _ _
    have e1 : (up j hj σ y).1 = GlobalTheory.IrrAn.pt q (σ.comp β) y ≫ toGen j hj σ := by
      apply pullback.hom_ext
      · rw [d1, Category.assoc, b1, ← Category.assoc, c1]
      · rw [d2, Category.assoc, b2, ← Category.assoc, c2, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, a1, ← e1]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, a2, c2]; exact pullback.lift_snd _ _ _
  exact congrArg (fun g : Sp ℂ ⟶ genCx Z σ => g (IsLocalRing.closedPoint ℂ)) e

end

theorem exists_up_mem_ptsOf_component : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ C ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), ∀ T : Set Y, IsClosed T → genericPoint Y ∉ T → ∃ y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)), up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' C) ∧ y.1 (IsLocalRing.closedPoint ℂ) ∉ T := by
  intro D A N j S κ s σ Y _ q jm _ hq n hY C hC T hT hη
  have : LocallyOfFiniteType q := by
    obtain ⟨m, i, hi, e⟩ := hY.isProjOver
    rw [← e]
    have := isProper_str (𝓞 κ.c.F) m
    infer_instance
  obtain ⟨y, hyC, hyT⟩ := exists_cxPt_component_notMem (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))
    (σ.injective.comp (RingOfIntegers.coe_injective)) q C hC T hT hη
  exact ⟨y, ⟨_, hyC, (ptOf_up_eq_toGenCx_pt jm hq σ y).symm⟩, hyT⟩

end GlobalTheory.HorComp

end
