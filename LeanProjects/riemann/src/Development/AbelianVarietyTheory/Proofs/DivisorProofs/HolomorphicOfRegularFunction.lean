import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
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
open GlobalTheory.IrrAn

noncomputable section

namespace GlobalTheory.IrrAn

open Limits

variable {k : Type} [CommRing k] {X : Scheme.{0}}

def ptC (p : X ⟶ Sp k) (σ : k →+* ℂ) (y : CxPts p σ) :
    CxPts (pullback.snd p (spMap σ)) (RingHom.id ℂ) :=
  ⟨pt p σ y, (pullback.lift_snd _ _ _).trans (Spec.map_id _).symm⟩

theorem pt_comp_fst (p : X ⟶ Sp k) (σ : k →+* ℂ) (y : CxPts p σ) :
    pt p σ y ≫ pullback.fst p (spMap σ) = y.1 := pullback.lift_fst _ _ _

theorem valR_appLE_hol {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, U)) :
    valR x W (g.appLE U W e f) = valR (x ≫ g) U f := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun a ha => e (h ha)
  rw [valR, valR, dif_pos h, dif_pos h']
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem ptC_mem {p : X ⟶ Sp k} {σ : k →+* ℂ} {U : X.Opens} {y : CxPts p σ} (h : y ∈ ptsIn p σ U) :
    ptC p σ y ∈ ptsIn (pullback.snd p (spMap σ)) (RingHom.id ℂ) (pullback.fst p (spMap σ) ⁻¹ᵁ U) := by
  change ⊤ ≤ pt p σ y ⁻¹ᵁ (pullback.fst p (spMap σ) ⁻¹ᵁ U)
  rw [← Scheme.Hom.comp_preimage, pt_comp_fst]
  exact h

theorem holoOn_preimage_affine {p : X ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} (R : AnRead p σ d)
    {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(pullback p (spMap σ), pullback.fst p (spMap σ) ⁻¹ᵁ U)) :
    R.HoloOn (ptsIn p σ U) fun y => ev _ (RingHom.id ℂ) _ f (ptC p σ y) := by
  have H := IsPullback.of_hasPullback p (spMap σ)
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    (UY := pullback.fst p (spMap σ) ⁻¹ᵁ U) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hf : f ∈ Subring.closure _ :=
    (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top f)
  have hc : ∀ c : ℂ, R.HoloOn (ptsIn p σ U) fun _ => c := fun c _ => differentiableOn_const c
  induction hf using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · refine (R.holoOn_ev U a).congr fun y hy => ?_
      exact (valR_appLE_hol _ _ _ _ _ (ptC_mem hy) a).trans
        (congrArg (fun z => valR z U a) (pt_comp_fst p σ y))
    · refine (hc (valR (spMap (RingHom.id ℂ)) ⊤ a)).congr fun y hy => ?_
      exact (valR_appLE_hol _ _ _ _ _ (ptC_mem hy) a).trans
        (congrArg (fun z => valR z ⊤ a) (ptC p σ y).2)
  | zero => exact (hc 0).congr fun y hy => by rw [ev_eq (ptC_mem hy), map_zero]
  | one => exact (hc 1).congr fun y hy => by rw [ev_eq (ptC_mem hy), map_one]
  | add x y _ _ hx hy =>
    have : R.HoloOn (ptsIn p σ U) fun z => ev _ (RingHom.id ℂ) _ x (ptC p σ z) +
      ev _ (RingHom.id ℂ) _ y (ptC p σ z) := fun i => (hx i).add (hy i)
    exact this.congr fun z _ => ev_add _ _ _
  | neg x _ hx =>
    have : R.HoloOn (ptsIn p σ U) fun z => - ev _ (RingHom.id ℂ) _ x (ptC p σ z) :=
      fun i => (hx i).neg
    exact this.congr fun z hz => by rw [ev_eq (ptC_mem hz), ev_eq (ptC_mem hz), map_neg]
  | mul x y _ _ hx hy => exact (hx.mul hy).congr fun z _ => ev_mul _ _ _

theorem holoOn_valR_pt (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)
    (R : AnRead p σ d) (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens)
    (h : Γ(Limits.pullback p (spMap σ), W)) :
    R.HoloOn (GlobalTheory.IrrAn.ptsOf p σ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0})))
      (fun y => valR (GlobalTheory.IrrAn.pt p σ y) W h) := by
  refine AnRead.holoOn_of_cover (ι := X.affineOpens) (T := fun U => ptsIn p σ U.1)
    (fun U => isOpen_ptsIn _) (fun y _ => exists_mem_ptsIn (iSup_affineOpens_eq_top X) y)
    fun U i => ?_
  have : IsAffineHom (pullback.fst p (spMap σ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hU' : IsAffineOpen (pullback.fst p (spMap σ) ⁻¹ᵁ U.1) := U.2.preimage _
  have key := (holo_of_affine (p := pullback.snd p (spMap σ)) (σ := RingHom.id ℂ) hU'
    (s := fun v => ptC p σ ((R.chart i).e.symm v))
    ((R.chart i).e.isOpen_inter_preimage_symm (isOpen_ptsIn U.1))
    (fun v hv => ptC_mem hv.2) (fun a => holoOn_preimage_affine R U.2 a i)).2 W h
  exact key.mono fun v hv => ⟨⟨hv.1, hv.2.2⟩, mem_ptsIn.2 hv.2.1⟩

end GlobalTheory.IrrAn

end
