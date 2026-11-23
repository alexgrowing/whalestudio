import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple

open GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

theorem pull_toPic_eq_zero_of_isEqn {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (U : X.Opens)
    (g : X.functionFieldˣ) (h : ∀ y ∈ U, D.IsEqn y g) : CechPic.pull U.ι (toPic D) = 0 := by
  classical
  rw [toPic_apply, ← cls_pull (isLB_toLB D) U.ι (pull_isLB (isLB_toLB D) U.ι), cls_eq_zero_iff]
  have key (i : (toLB D).ι) : ∃ a : Γ(X, (toLB D).U i ⊓ U)ˣ, ∀ hU, fnOf _ hU a.val =
      (i.1.2 : X.functionField) / (g : X.functionField) :=
    exists_unit_fnOf_eq fun x hx => (h x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  choose a ha using key
  have hle (J : PUnit → (toLB D).ι) : ((toLB D).pull U.ι).U J ≤ U.ι ⁻¹ᵁ ((toLB D).U (J PUnit.unit) ⊓ U) :=
    fun y hy => ⟨mem_pull.1 hy, y.2⟩
  refine ⟨⟨fun J => res (hle J) (pullU U.ι _ (a (J PUnit.unit)))⟩, (isGen_iff_germ _).2 fun y I J hI hJ => ?_⟩
  have hI' := mem_pull.1 hI
  have hJ' := mem_pull.1 hJ
  have hm : U.ι y ∈ (toLB D).U (I PUnit.unit) ⊓ (toLB D).U (J PUnit.unit) ⊓ U := ⟨⟨hI', hJ'⟩, y.2⟩
  have e : res (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a (I PUnit.unit)) =
      res inf_le_left ((toLB D).g (I PUnit.unit) (J PUnit.unit)) *
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a (J PUnit.unit)) :=
    Units.ext (Cartier.fn_ext fun hU => by
      rw [Units.val_mul, map_mul]
      simp only [LB.val_res, fnOf_resG, ha, fnOf_toLB_g]
      exact (div_mul_div_cancel₀ (Units.ne_zero (J PUnit.unit).1.2)).symm)
  have e' := (congrArg (gm U.ι y _) e).trans (map_mul _ _ _)
  erw [gm_res _ _ _ hm, gm_res _ _ _ hm, gm_res _ _ _ hm] at e'
  have hI2 : U.ι ((𝟙 U.toScheme : U.toScheme ⟶ U.toScheme) y) ∈ (toLB D).U (I PUnit.unit) ⊓ U := ⟨hI', y.2⟩
  have hJ2 : U.ι ((𝟙 U.toScheme : U.toScheme ⟶ U.toScheme) y) ∈ (toLB D).U (J PUnit.unit) ⊓ U := ⟨hJ', y.2⟩
  have a1 := gm_pull (𝟙 _) U.ι y _ hI2 (a (I PUnit.unit))
  have a2 := gm_pull (𝟙 _) U.ι y _ hJ2 (a (J PUnit.unit))
  have a3 := gm_pull_g (toLB D) U.ι (𝟙 _) y I J hI hJ
  rw [Category.id_comp] at a1 a2 a3
  rw [gm_res _ _ _ hI, gm_res _ _ _ hJ]
  exact a1.trans (e'.trans (congrArg₂ (· * ·) a3.symm a2.symm))

end GlobalTheory.FlagAmple

namespace GlobalTheory.FlagAmple

open GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv
open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

def germAt (C : FlagCpt Z e) (V : (gen Z).Opens) {y : C.Y.X} (hy : y ∈ C.π ⁻¹ᵁ V) :
    Γ(gen Z, V) →+* C.Y.X.presheaf.stalk y :=
  (C.Y.X.presheaf.germ (C.π ⁻¹ᵁ V) y hy).hom.comp (C.π.app V).hom

theorem spMap_germAt (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {y : C.Y.X}
    (hy : y ∈ C.π ⁻¹ᵁ V) : spMap (germAt C V hy) ≫ hV.fromSpec = stalkPt C.Y y ≫ C.π := by
  obtain ⟨W, hW, hyW, h⟩ := exists_isAffineOpen_mem_and_subset (X := C.Y.X) (U := C.π ⁻¹ᵁ V) (x := y) hy
  have e1 : (C.Y.X.presheaf.germ W y hyW).hom.comp (C.π.appLE V W h).hom = germAt C V hy :=
    RingHom.ext fun a => C.Y.X.presheaf.germ_res_apply (homOfLE h) y hyW _
  have hρ : spMap (C.π.appLE V W h).hom ≫ hV.fromSpec = hW.fromSpec ≫ C.π :=
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hW h
  rw [← e1, ← spMap_comp_spMap, Category.assoc, hρ, ← Category.assoc, Spread.spMap_germ]
  rfl

theorem algebraMap_comp_germAt (C : FlagCpt Z e) (V : (gen Z).Opens) {y : C.Y.X} (hy : y ∈ C.π ⁻¹ᵁ V)
    (hη : genericPoint C.Y.X ∈ C.π ⁻¹ᵁ V) :
    (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp (germAt C V hy) = germAt C V hη :=
  RingHom.ext fun a => algebraMap_germ hy _

theorem isEqn_sum {X : Scheme.{0}} [IsIntegral X] {κ : Type} (s : Finset κ) (Dv : κ → CartierDiv X)
    (u : κ → X.functionFieldˣ) {y : X} (h : ∀ a, (Dv a).IsEqn y (u a)) :
    (∑ a ∈ s, Dv a).IsEqn y (∏ a ∈ s, u a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isEqn_zero y
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).add ih

theorem exists_isEqn_detDiv (C : FlagCpt Z e) (V : (gen Z).Opens) (hV : IsAffineOpen V) (φ : c.F →+* Γ(gen Z, V))
    (g : EigFrame Z φ (hV.fromSpec ≫ genι Z)) (hs : hV.fromSpec ≫ genStr Z = spMap φ) (τ : E →+* ℂ) :
    ∃ G : C.Y.Fnˣ, ∀ y ∈ C.π ⁻¹ᵁ V, (detDiv C τ (Dw.mult τ)).IsEqn y G := by
  classical
  by_cases hη : genericPoint C.Y.X ∈ C.π ⁻¹ᵁ V
  swap
  · exact ⟨1, fun y hy => (hη (gen_mem hy)).elim⟩
  let ψ : Γ(gen Z, V) →+* C.Y.Fn := germAt C V hη
  have hψx : spMap ψ ≫ hV.fromSpec ≫ genι Z = genericPt C.Y ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, spMap_germAt]; rfl
  have hψφ : ψ.comp φ = constF e C.Y := by
    letI := (constF e C.Y).toAlgebra
    have h1 : (genericPt C.Y ≫ C.π) ≫ genStr Z = spMap (constF e C.Y) :=
      (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) Z.jQ_over).trans (ptF_snd C.y0)))
    have h2 : spMap (ψ.comp φ) = spMap (constF e C.Y) := by
      rw [← spMap_comp_spMap, ← hs, ← Category.assoc, spMap_germAt]
      exact h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  obtain ⟨g', hg'⟩ := Spread.exists_bc g ψ hψφ hψx
  obtain ⟨A, B, hBA, hA⟩ := Spread.exists_coord g' C.f0 τ
  have hdet : IsUnit A.det := by
    have := congrArg Matrix.det hBA
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans this)
  refine ⟨hdet.unit, fun y hy => ?_⟩
  obtain ⟨φ₁, f, t, hT, ht⟩ := C.gr_spec y
  let j := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField
  have hj : j.comp (germAt C V hy) = ψ := algebraMap_comp_germAt C V hy hη
  have hφy : (germAt C V hy).comp φ = φ₁ := RingHom.ext fun r =>
    IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField
      ((RingHom.congr_fun hj (φ r)).trans ((RingHom.congr_fun hψφ r).trans (RingHom.congr_fun hT.2.1 r)))
  have hxy : spMap (germAt C V hy) ≫ hV.fromSpec ≫ genι Z = stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, spMap_germAt, Category.assoc]
  obtain ⟨gy, hgy⟩ := Spread.exists_bc g (germAt C V hy) hφy hxy
  obtain ⟨Ay, By, hBAy, hAy⟩ := Spread.exists_coord gy f τ
  obtain ⟨fj, hfj⟩ := Spread.exists_bc f j hT.2.1.symm hT.1.symm
  choose cf hcf1 hcf2 hcf3 using hT.2.2 τ
  have hf0 : ∀ i, C.f0.vec τ i = ∑ k, cf i k • fj.vec τ k := fun i => by
    have e : (fun k => spMap (dualMap j) ≫ f.v τ k) = fun k => (tv (fj.vec τ k)).left :=
      funext fun k => (congrArg (fun v => (tv v).left) (hfj τ k)).symm
    have h := hcf3 i
    rw [e] at h
    exact (isComb_iff (fj.vec τ) (cf i) (C.f0.vec τ i)).1 h
  have hfj' : ∀ k, fj.vec τ k = ∑ l, j (Ay k l) • g'.vec τ l := fun k => by
    rw [hfj, hAy, res_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgy, res_res _ hxy j hT.1.symm hj hψx, ← hg']
  have hAeq : A = Matrix.of cf * Ay.map j := by
    refine Matrix.ext fun i l => congrFun ((g'.existsUnique_sum τ (C.f0.vec τ i) (C.f0.act_vec τ i)).unique
      (hA i) ?_) l
    rw [hf0]
    simp only [hfj', Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hlow : (Matrix.of cf).BlockTriangular OrderDual.toDual := fun i k hik => hcf2 i k hik
  have hdetA : A.det = (∏ i, (t τ i : C.Y.Fn)) * j Ay.det := by
    rw [hAeq, Matrix.det_mul, Matrix.det_of_lowerTriangular _ hlow, RingHom.map_det]
    simp only [Matrix.of_apply, hcf1]
    rfl
  have hunit : IsUnit Ay.det := by
    have := congrArg Matrix.det hBAy
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans this)
  have hsum : (detDiv C τ (Dw.mult τ)).IsEqn y (∏ i, t τ i) := by
    have e : detDiv C τ (Dw.mult τ) = ∑ a : Fin (Dw.mult τ), C.gr τ a := by
      simp only [detDiv, Fin.is_lt, if_true]
    rw [e]
    exact isEqn_sum _ _ _ fun a => ht τ a
  refine hsum.iff_unitAt.2 ⟨Ay.det, hunit, ?_⟩
  rw [IsUnit.unit_spec, hdetA, Units.coe_prod, mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.2 fun i _ => (t τ i).ne_zero)]

end Frame

end GlobalTheory.FlagAmple

namespace GlobalTheory.FlagAmple

theorem topDet_pull_eq_zero : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ τ : D.host.E →+* ℂ, GlobalTheory.CechPic.pull ((Φ.C k).π ⁻¹ᵁ V).ι (toPic (GlobalTheory.FlagAmple.detDiv (Φ.C k) τ (S.Dw.mult τ))) = 0 := by
  intro D A N j S κ s Φ k V hV φ g hs _ τ
  obtain ⟨G, hG⟩ := exists_isEqn_detDiv (Φ.C k) V hV φ g hs τ
  exact pull_toPic_eq_zero_of_isEqn _ _ G hG

end GlobalTheory.FlagAmple
