import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCoordinatesLocallyConstantUpToUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGradedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigDiv

theorem exists_eigFrame_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (R : Type) [CommRing R] [IsLocalRing R] (p : Sp R ⟶ X₀ TF.Y Z), ∃ (φ : c.F →+* R) (_ : GlobalTheory.ShFam.EigFrame TF.Y φ (p ≫ (barComp TF.Y Z).ι)), p ≫ s₀ TF.Y Z = spMap φ := by
  intro E _ _ _ H Dw l Xo c TF Z R _ _ p
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let x : Sp R ⟶ GlobalTheory.Toroidal.gen TF.Y := (p ≫ (barComp TF.Y Z).ι) ≫ inv (GlobalTheory.Toroidal.genι TF.Y)
  let φ : c.F →+* R := (Spec.preimage (p ≫ s₀ TF.Y Z)).hom
  have hφ : spMap φ = p ≫ s₀ TF.Y Z := Spec.map_preimage _
  have hx : x ≫ GlobalTheory.Toroidal.genStr TF.Y = spMap φ := by
    rw [hφ, Category.assoc, hs, Category.assoc]
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y R φ x hx
  have e : x ≫ GlobalTheory.Toroidal.genι TF.Y = p ≫ (barComp TF.Y Z).ι := by
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨φ, e ▸ f, hφ.symm⟩

theorem ratio_mem {K : Type} [Field K] (S : Subgroup Kˣ) {ι : Type} [Fintype ι] (u v w : ι → Kˣ)
    (h : ∀ τ, (v τ : K) = w τ * u τ) (hw : ∀ τ, w τ ∈ S) (a : ι → ℤ) :
    (∏ τ, u τ ^ (-a τ)) / (∏ τ, v τ ^ (-a τ)) ∈ S := by
  have hv : ∀ τ, v τ = w τ * u τ := fun τ => Units.ext (by rw [Units.val_mul]; exact h τ)
  rw [← Finset.prod_div_distrib]
  refine S.prod_mem fun τ _ => ?_
  have e : u τ / v τ = (w τ)⁻¹ := by rw [hv, div_mul_eq_div_div_swap, div_self', one_div]
  rw [← div_zpow, e]
  exact S.zpow_mem (S.inv_mem (hw τ)) _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] (g : X → X.functionFieldˣ)
    (h : ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, UnitAt y ((g x : X.functionField) / g y)) :
    ∃ D : CartierDiv X, ∀ x, D.IsEqn x (g x) :=
  ⟨show cartierGroup X from ⟨fun x => germOf x (g x), fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, g x, fun y hy => germOf_eq_iff.2 (hU y hy)⟩⟩, fun _ => rfl⟩

theorem exists_detDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  intro E _ _ _ H Dw l Xo c TF Z _
  have hloc : ∀ x : X₀ TF.Y Z, IsLocalRing ((X₀ TF.Y Z).presheaf.stalk x) := fun x => inferInstance
  obtain ⟨φ₀, f₀, h₀⟩ := @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk (genericPoint (X₀ TF.Y Z))) _ (hloc _) ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)))
  refine ⟨φ₀, f₀, h₀, fun a => ?_⟩
  choose φx fx hx using fun x : X₀ TF.Y Z => @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk x) _ (hloc x) ((X₀ TF.Y Z).fromSpecStalk x)
  have hpt : ∀ x : X₀ TF.Y Z, spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫
      (X₀ TF.Y Z).fromSpecStalk x = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) := fun x =>
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hφ : ∀ x, φ₀ = (algebraMap _ (X₀ TF.Y Z).functionField).comp (φx x) := fun x =>
    GlobalTheory.ShFam.EigLoc.spMap_inj (by rw [← h₀, ← hpt x, Category.assoc, hx x]; exact (Spec.map_comp _ _).symm)
  choose fK hfK using fun x => (fx x).exists_isMap (algebraMap _ (X₀ TF.Y Z).functionField) (hφ x)
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (by rw [← hpt x]; exact Category.assoc _ _ _)
  let g : ∀ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
    (X₀ TF.Y Z).functionFieldˣ := fun fK => ∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ)
  have key : ∀ (y : X₀ TF.Y Z) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)),
      (∀ τ, UnitAt y (fK'.co fK τ).det) → UnitAt y ((g fK : (X₀ TF.Y Z).functionField) / g fK') := by
    intro y fK fK' hu
    have := ratio_mem (unitsAt y) (fun τ => (fK.isUnit_det_co f₀ τ).unit) (fun τ => (fK'.isUnit_det_co f₀ τ).unit)
      (fun τ => (fK'.isUnit_det_co fK τ).unit) (fun τ => by
        simp only [IsUnit.unit_spec]
        rw [← Matrix.det_mul, GlobalTheory.ShFam.EigFrame.co_mul]) (fun τ => hu τ) a
    rw [← Units.val_div_eq_div_val (g fK) (g fK')]
    exact this
  obtain ⟨D, hD⟩ := exists_div (fun x => g (fK x)) fun x => by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x (φx x) (fx x) (hx x)
    exact ⟨U, hxU, fun y hy => key y _ _ (hU y hy (φx y) (fx y) φ₀ (fK x) (fK y) (hx y) h₀ (hfK x) (hfK y))⟩
  refine ⟨D, ?_, fun x => ⟨φx x, fx x, fun τ => (fK x |>.co f₀ τ).transpose,
    fun τ => (fK x |>.isUnit_det_co f₀ τ).unit, hx x, fun τ => (IsUnit.unit_spec _).trans (Matrix.det_transpose _).symm, fun τ i => ?_, hD x⟩⟩
  · refine GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines E H Dw l Xo c TF Z φ₀ f₀ a D h₀ fun x φ f fK' hs hm => ?_
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x φ f hs
    exact (hD x).iff_unitAt.2 (key x _ _ (hU x hxU (φx x) (fx x) φ₀ fK' (fK x) (hx x) h₀ hm (hfK x)))
  · have e : (fK x).v τ = fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x)
        (X₀ TF.Y Z).functionField)) ≫ (fx x).v τ k := funext (hfK x τ)
    rw [← e]
    exact (fK x).co_spec f₀ τ i

end GlobalTheory.EigDiv
