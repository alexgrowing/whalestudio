import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

noncomputable section

namespace GlobalTheory.FlagCov

theorem evalPt_genPt_comp {X Y : Scheme.{0}} [IsIntegral X] (j : X ⟶ Y) (W : Y.Opens)
    (hx : ⊤ ≤ (GlobalTheory.FlagCov.genPt X ≫ j) ⁻¹ᵁ W) (h : genericPoint X ∈ j ⁻¹ᵁ W) (a : Γ(Y, W)) :
    TangentOrigin.evalPt (GlobalTheory.FlagCov.genPt X ≫ j) W hx a = fnOf (j ⁻¹ᵁ W) h ((j.app W).hom a) := by
  have e : (X.fromSpecStalk (genericPoint X)).appLE (j ⁻¹ᵁ W) ⊤ hx ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom =
      X.presheaf.germ (j ⁻¹ᵁ W) (genericPoint X) h := by
    have k : ∀ (V : X.Opens) (h : genericPoint X ∈ V) (hx : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V),
        (X.fromSpecStalk (genericPoint X)).appLE V ⊤ hx ≫
          (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom =
        X.presheaf.germ V (genericPoint X) h := by
      intro V h hx
      simp only [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h, Category.assoc]
      rw [← Functor.map_comp_assoc, Subsingleton.elim ((homOfLE le_top).op ≫ (homOfLE hx).op) (𝟙 _), CategoryTheory.Functor.map_id,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    exact k _ h hx
  have e2 := Scheme.Hom.comp_appLE (X.fromSpecStalk (genericPoint X)) j W ⊤ hx
  change ((X.fromSpecStalk (genericPoint X) ≫ j).appLE W ⊤ hx ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom).hom a = _
  rw [e2, Category.assoc, e]
  rfl

theorem resM_frame_eq_detUnit_smul {Y : Scheme.{0}} {F : Y.Modules} {U U' V : Y.Opens}
    {e : Fin 1 → Γ(F, U)} {e' : Fin 1 → Γ(F, U')} (he : VB.IsFrame e) (he' : VB.IsFrame e')
    (h : V ≤ U) (h' : V ≤ U') :
    Twist.resM F h' (e' 0) = (he.detUnit he' h h' : Γ(Y, V)) • Twist.resM F h (e 0) := by
  rw [VB.IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]
  have := (he.basis h).sum_repr (Twist.resM F h' (e' 0))
  rw [Fin.sum_univ_one, VB.IsFrame.basis_apply] at this
  exact this.symm

theorem fnOf_pull_g {X Y : Scheme.{0}} [IsIntegral X] (j : X ⟶ Y) (L : LB Y) (c c' : (L.pull j).ι)
    (h : genericPoint X ∈ (L.pull j).U c ⊓ (L.pull j).U c')
    (h' : genericPoint X ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit))) :
    fnOf _ h ((L.pull j).g c c' : Γ(X, _)) =
      fnOf _ h' ((j.app _).hom (L.g (c PUnit.unit) (c' PUnit.unit) : Γ(Y, _))) := by
  have e : (L.pull j).g c c' = Semi.res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => j) c PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => j) c' PUnit.unit)))
      (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    have k : ∀ {G : Type} [CommGroup G] (f : PUnit.{1} → G),
        ∏ k, f k ^ (1 : ℤ) = f PUnit.unit := fun f => by simp
    exact k (G := Γ(X, LB.wchart L (fun _ : PUnit.{1} => j) c ⊓ LB.wchart L (fun _ : PUnit.{1} => j) c')ˣ)
      (fun u => Semi.res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => j) c u))
        (inf_le_right.trans (LB.wchart_le L (fun _ => j) c' u))) (pullU j _ (L.g (c u) (c' u))))
  rw [e]
  exact fnOf_resG _ h _

theorem isRatSec_pull_root_of_scaling : ∀ {X Y₀ : Scheme.{0}} [IsIntegral X] (j : X ⟶ Y₀) {M : Y₀.Modules} {N : ℕ} (fl : Vert.Flag M N) (i : Fin N)
    (r : ((fl.root i).pull j).ι → X.functionFieldˣ),
    (∀ ch ch' : ((fl.root i).pull j).ι, genericPoint X ∈ ((fl.root i).pull j).U ch ⊓ ((fl.root i).pull j).U ch' →
      ∃ (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) (hx : ⊤ ≤ (GlobalTheory.FlagCov.genPt X ≫ j) ⁻¹ᵁ W)
        (lam : Γ(fl.F i.succ, W) → X.functionField),
        (∀ (s : Γ(Y₀, W)) (t : Γ(fl.F i.succ, W)), lam (s • t) = TangentOrigin.evalPt (GlobalTheory.FlagCov.genPt X ≫ j) W hx s * lam t) ∧
        (∃ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0)) ∧
        (∀ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0) →
          lam t = ((r ch)⁻¹ : X.functionFieldˣ)) ∧
        (∀ t : Γ(fl.F i.succ, W), (fl.π i).app W t = Twist.resM _ (hW.trans inf_le_right) ((ch' PUnit.unit).e 0) →
          lam t = ((r ch')⁻¹ : X.functionFieldˣ))) →
    IsRatSec ((fl.root i).pull j) r := by
  intro X Y₀ _ j M N fl i r H ch ch' h
  obtain ⟨W, hW, hx, lam, hlam, ⟨t, ht⟩, h1, h2⟩ := H ch ch' h
  have hWj : genericPoint X ∈ j ⁻¹ᵁ W := by
    have := hx (Set.mem_univ (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))))
    change j ((X.fromSpecStalk (genericPoint X)) (IsLocalRing.closedPoint _)) ∈ W at this
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have h' : genericPoint X ∈ j ⁻¹ᵁ ((ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) := hW hWj
  have hx' : ⊤ ≤ (GlobalTheory.FlagCov.genPt X ≫ j) ⁻¹ᵁ ((ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) :=
    fun y hy => hW (hx hy)
  set g : Γ(Y₀, W)ˣ := (ch PUnit.unit).isFrame.detUnit (ch' PUnit.unit).isFrame
    (hW.trans inf_le_left) (hW.trans inf_le_right) with hg
  have e1 := h2 ((g : Γ(Y₀, W)) • t) (by
    rw [Scheme.Modules.Hom.app_smul, ht]
    exact (resM_frame_eq_detUnit_smul _ _ _ _).symm)
  rw [hlam, h1 t ht] at e1
  have e2 : TangentOrigin.evalPt (GlobalTheory.FlagCov.genPt X ≫ j) W hx (g : Γ(Y₀, W)) =
      fnOf _ h (((fl.root i).pull j).g ch ch' : Γ(X, _)) := by
    rw [fnOf_pull_g j (fl.root i) ch ch' h h']
    refine Eq.trans ?_ (evalPt_genPt_comp j _ hx' h' _)
    refine Eq.trans ?_ (TangentOrigin.evalPt_res _ hW hx' hx _)
    refine congrArg _ ?_
    exact (congrArg Units.val (VB.IsFrame.res_detUnit (ch PUnit.unit).isFrame (ch' PUnit.unit).isFrame
      inf_le_left inf_le_right hW)).symm
  rw [e2, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val] at e1
  have a := (r ch).ne_zero
  have b := (r ch').ne_zero
  field_simp at e1
  linear_combination -e1

end GlobalTheory.FlagCov
