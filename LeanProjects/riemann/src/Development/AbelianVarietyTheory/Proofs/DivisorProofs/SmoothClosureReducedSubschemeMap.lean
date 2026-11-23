import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackPieceIsoFactor
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CloFlag

open GlobalTheory.CovTest.BCFlag

def sqIso {P Y B' B : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ B'} {π : Y ⟶ B} {g : B' ⟶ B} (c : a ≫ π = b ≫ g) (E : B.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback π).obj E) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj E) :=
  (Scheme.Modules.pullbackComp a π).app E ≪≫ (Scheme.Modules.pullbackCongr c).app E ≪≫
    ((Scheme.Modules.pullbackComp b g).app E).symm

theorem sq_key {T P Y B' B : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ B'} {π : Y ⟶ B} {g : B' ⟶ B} (c : a ≫ π = b ≫ g)
    (f : T ⟶ P) (h : T ⟶ Y) (t : T ⟶ B') (ha : f ≫ a = h) (hb : f ≫ b = t) (w : h ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback a).map ιF ≫ (sqIso c E).hom) ≫
        (Scheme.Modules.pullbackComp f b).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) ≫
            (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullbackComp f a).hom.app F ≫
        (Scheme.Modules.pullbackCongr ha).hom.app F ≫ (Scheme.Modules.pullback h).map ιF ≫
          (Scheme.Modules.pullbackComp h π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
  rw [← (Scheme.Modules.pullbackCongr ha).hom.naturality_assoc,
    ← (Scheme.Modules.pullbackComp f a).hom.naturality_assoc, pc_coh f a b π g c h t ha hb w E]
  simp only [sqIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, CategoryTheory.Functor.map_comp,
    Category.assoc, Functor.comp_map]

theorem isFlagBundle_of_isPullback {P Y B' B : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ B'} {π : Y ⟶ B} {g : B' ⟶ B}
    (sq : IsPullback a b π g) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ x, Vert.Flag ((Scheme.Modules.pullback π).obj (E x)) (n x)) (H : IsFlagBundle π E n fl) :
    IsFlagBundle b (fun x => (Scheme.Modules.pullback g).obj (E x)) n
      (fun x => ((fl x).pull a).ofIso (sqIso sq.w (E x))) := by
  intro T t fl''
  obtain ⟨h, ⟨w, he⟩, hu⟩ := H T (t ≫ g) (fun x => (fl'' x).ofIso ((Scheme.Modules.pullbackComp t g).app (E x)))
  refine ⟨sq.lift h t w, ⟨sq.lift_snd _ _ _, fun x i => ?_⟩, ?_⟩
  · obtain ⟨e, hee⟩ := he x i
    refine ⟨(Scheme.Modules.pullbackComp (sq.lift h t w) a).app ((fl x).F i) ≪≫
      (Scheme.Modules.pullbackCongr (sq.lift_fst h t w)).app ((fl x).F i) ≪≫ e, ?_⟩
    have k := sq_key sq.w (sq.lift h t w) h t (sq.lift_fst h t w) (sq.lift_snd h t w) w (E x) ((fl x).F i) ((fl x).ι i)
    have hee' : e.hom ≫ (fl'' x).ι i ≫ (Scheme.Modules.pullbackComp t g).hom.app (E x) = _ := hee
    rw [← hee'] at k
    rw [← cancel_mono ((Scheme.Modules.pullbackComp t g).hom.app (E x))]
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    exact k.symm
  · rintro y ⟨w'', he''⟩
    have w₁ : (y ≫ a) ≫ π = t ≫ g := by rw [Category.assoc, sq.w, ← Category.assoc, w'']
    apply sq.hom_ext
    · rw [sq.lift_fst]
      refine hu _ ⟨w₁, fun x i => ?_⟩
      obtain ⟨e, hee⟩ := he'' x i
      refine ⟨((Scheme.Modules.pullbackComp y a).app ((fl x).F i)).symm ≪≫ e, ?_⟩
      have k := sq_key sq.w y _ t rfl w'' w₁ (E x) ((fl x).F i) ((fl x).ι i)
      have e1 : (Scheme.Modules.pullbackCongr (rfl : y ≫ a = y ≫ a)).hom.app ((fl x).F i) = 𝟙 _ := by
        simp [Scheme.Modules.pullbackCongr]
      have hee₀ : e.hom ≫ (fl'' x).ι i =
          (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback a).map ((fl x).ι i) ≫ (sqIso sq.w (E x)).hom) ≫
            (Scheme.Modules.pullbackComp y b).hom.app ((Scheme.Modules.pullback g).obj (E x)) ≫
              (Scheme.Modules.pullbackCongr w'').hom.app ((Scheme.Modules.pullback g).obj (E x)) := hee
      rw [e1, Category.id_comp] at k
      have k' : e.hom ≫ (fl'' x).ι i ≫ (Scheme.Modules.pullbackComp t g).hom.app (E x) = _ :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Scheme.Modules.pullbackComp t g).hom.app (E x)) hee₀).trans
          (((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).trans k))
      exact (Category.assoc _ _ _).trans ((congrArg ((Scheme.Modules.pullbackComp y a).inv.app ((fl x).F i) ≫ ·) k').trans
        (Iso.inv_hom_id_app_assoc _ _ _))
    · rw [sq.lift_snd, w'']

theorem exists_isPullback_clo {X Y : Scheme.{0}} (π : Y ⟶ X) [Smooth π] {y : Y} {z : X}
    (h : closure {y} = π ⁻¹' closure {z}) :
    ∃ ρ : _ ⟶ _, IsPullback (redι (clo y)) ρ π (redι (clo z)) := by
  let j := Limits.pullback.fst π (redι (clo z))
  have : IsReduced (Limits.pullback π (redι (clo z))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (Limits.pullback.snd π (redι (clo z)))
  have hj : Set.range j = closure {y} := by
    rw [h, ← show Set.range (redι (clo z)) = closure {z} from range_redι (clo z)]
    exact Scheme.Pullback.range_fst π _
  have hk : j.ker = (redι (clo y)).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← InterModel.radical_ker j, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, hj, closure_closure]
    rfl
  let f := IsClosedImmersion.lift j (redι (clo y)) hk.le
  have hf : f ≫ j = redι (clo y) := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_of_ker_eq _ _ f hf hk.symm
  refine ⟨f ≫ Limits.pullback.snd π (redι (clo z)), ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso f) hf rfl
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, hf]

theorem isometric_pull_sq {k : Type} [CommRing k] {P Y B' B : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ B'} {π : Y ⟶ B} {g : B' ⟶ B}
    (c : a ≫ π = b ≫ g) {p : B ⟶ Sp k} (N : HermLB p) (w : b ≫ g ≫ p = a ≫ π ≫ p) :
    ((N.pull π rfl).pull a rfl).Isometric ((N.pull g rfl).pull b w) := by
  have key {Z : Scheme.{0}} (u : P ⟶ Z) (v : Z ⟶ B) (t : P ⟶ B) (ht : u ≫ v = t) (hu : u ≫ v ≫ p = a ≫ π ≫ p)
      (ht' : t ≫ p = a ≫ π ≫ p) : (N.pull t ht').Isometric ((N.pull v rfl).pull u hu) := by
    subst ht
    have R := N.refines_pull_comp v rfl u hu ht'
    exact HermLB.isometric_of_chart _ R.le (fun x => R.g _ (𝟙 _) x)
      fun σ c y hy => ((R.φ σ c y hy).trans (add_zero _)).symm
  exact (key a π _ rfl rfl (Category.assoc _ _ _)).symm.trans (key b g _ c.symm w (Category.assoc _ _ _))

theorem exists_isFlagBundle_clo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p) (z : X) (y : F.Y), Smooth F.π → closure {y} = F.π ⁻¹' closure {z} → ∃ (ρ : (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme ⟶ (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme) (_ : ρ ≫ redι (clo z) = redι (clo y) ≫ F.π) (w : ρ ≫ redι (clo z) ≫ p = redι (clo y) ≫ F.π ≫ p) (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (redι (clo z))).obj E)) r), IsFlagBundle ρ (fun _ : Unit => (Scheme.Modules.pullback (redι (clo z))).obj E) (fun _ => r) (fun _ => fl) ∧ ((F.fam H N none).restr (redι (clo y))).Isometric ((N.restr (redι (clo z))).pull ρ w) ∧ ∀ i, ((F.fam H N (some i)).restr (redι (clo y))).Isometric (VMetric.grLB fl i ((H.pull (redι (clo z)) rfl).pull ρ w)) := by
  intro k _ X p E r h H F N z y _ hy
  obtain ⟨ρ, sq⟩ := exists_isPullback_clo F.π hy
  have w : ρ ≫ redι (clo z) ≫ p = redι (clo y) ≫ F.π ≫ p := by rw [← Category.assoc, ← sq.w, Category.assoc]
  refine ⟨ρ, sq.w.symm, w, (F.fl.pull (redι (clo y))).ofIso (sqIso sq.w E),
    isFlagBundle_of_isPullback sq (fun _ : Unit => E) (fun _ => r) (fun _ => F.fl) F.univ,
    isometric_pull_sq sq.w N w, fun i => ?_⟩
  have I : ((h.pull F.π rfl).pull (redι (clo y)) rfl).IsIsometry ((h.pull (redι (clo z)) rfl).pull ρ w)
      (sqIso sq.w E) := by
    obtain ⟨-, hc⟩ := VMetric.isIsometry_pull_id_comp k X p E r h
    have e₁ : (redι (clo y) ≫ F.π) ≫ p = redι (clo y) ≫ F.π ≫ p := Category.assoc _ _ _
    have e₂ : (ρ ≫ redι (clo z)) ≫ p = redι (clo y) ≫ F.π ≫ p := by rw [Category.assoc, w]
    have hc' {f f' : _ ⟶ X} (e : f = f') (hf : f ≫ p = redι (clo y) ≫ F.π ≫ p) (hf' : f' ≫ p = redι (clo y) ≫ F.π ≫ p) :
        (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
      subst e
      intro σ V s s' y hy
      rfl
    exact IsometryPullback.isIsometry_trans (hc _ _ _ _ F.π (redι (clo y)) rfl rfl e₁)
      (IsometryPullback.isIsometry_trans (hc' sq.w e₁ e₂) (IsometryPullback.isIsometry_symm (hc _ _ _ _ (redι (clo z)) ρ rfl w e₂)))
  rw [VMetric.grLB_ofIso I ((H.pull F.π rfl).pull _ rfl)]
  exact (VMetric.isometric_grLB_pull k F.Y _ _ _ _ r (h.pull F.π rfl) (H.pull F.π rfl) F.fl (redι (clo y)) rfl i).symm

end GlobalTheory.CloFlag

end
