import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoCotMapOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeProd

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_resM app_resM)

section Split

variable {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U V : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : VB.IsFrame e₁) (he₂ : VB.IsFrame e₂)

include h h₁ h₂ h₃ h₄ in

theorem repr_left (hV : V ≤ U) (y : Γ(F, V)) (i : Fin n) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.castAdd m i) =
      (he₁.basis hV).repr (i₁.app V y) i := by
  have key : (Finsupp.lapply (Fin.castAdd m i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₁.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₁ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₁]
      change _ = ((he₁.basis hV).repr ((resM F₁ hV) (e₁ j))) i
      rw [← IsFrame.basis_apply he₁ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₄]
      change _ = ((he₁.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem repr_right (hV : V ≤ U) (y : Γ(F, V)) (i : Fin m) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.natAdd n i) =
      (he₂.basis hV).repr (i₂.app V y) i := by
  have key : (Finsupp.lapply (Fin.natAdd n i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₂.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₂ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₃]
      change _ = ((he₂.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₂]
      change _ = ((he₂.basis hV).repr ((resM F₂ hV) (e₂ j))) i
      rw [← IsFrame.basis_apply he₂ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.natAdd_inj]
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem detUnit_append {U' : S.Opens} {e₁' : Fin n → Γ(F₁, U')} {e₂' : Fin m → Γ(F₂, U')}
    (he₁' : VB.IsFrame e₁') (he₂' : VB.IsFrame e₂') (hV : V ≤ U) (hV' : V ≤ U') :
    (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).detUnit
                 (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁' he₂') hV hV' =
      he₁.detUnit he₁' hV hV' * he₂.detUnit he₂' hV hV' := by
  refine Units.ext ?_
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).toMatrix
      (fun k => resM F hV' (Fin.append (fun i => p₁.app U' (e₁' i)) (fun j => p₂.app U' (e₂' j)) k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        ((he₁.basis hV).toMatrix fun i => resM F₁ hV' (e₁' i)) 0 0
        ((he₂.basis hV).toMatrix fun i => resM F₂ hV' (e₂' i))) := by
    ext k l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      simp only [Module.Basis.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fin.append_left,
        Fin.append_right, Matrix.zero_apply]
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₁]; rfl
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₄]
      change ((he₁.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₃]
      change ((he₂.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₂]; rfl
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Split

section Prod

open GlobalTheory.Conormal

variable {S : Scheme.{0}} (G H : Over S) [GrpObj G] [GrpObj H]

theorem lbIso_det_conormal_prod [QuasiSeparated G.hom] [QuasiSeparated H.hom] (g h : ℕ)
    (hG : IsVB (omega G) g) (hH : IsVB (omega H) h) (t : 𝟙_ (Over S) ⟶ G ⊗ H) (ht : t = lift η[G] η[H]) :
    LBIso (VB.det (conormal (sec t)) (g + h)) (CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)) := by
  subst ht
  have i₁ : η[G] ≫ lift (𝟙 G) (toUnit G ≫ η[H]) = lift η[G] η[H] := by simp
  have i₂ : η[H] ≫ lift (toUnit H ≫ η[G]) (𝟙 H) = lift η[G] η[H] := by simp
  have p₁ := lift_fst η[G] η[H]
  have p₂ := lift_snd η[G] η[H]
  have c₁ : η[H] ≫ toUnit H ≫ η[G] = η[G] := by simp
  have c₂ : η[G] ≫ toUnit G ≫ η[H] = η[H] := by simp
  have H₀ := cotMap_prod i₁ i₂ p₁ p₂
  have H₁ := (cotMap_comp p₁ i₁ (lift_fst _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₂ := (cotMap_comp p₂ i₂ (lift_snd _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₃ := (cotMap_comp p₁ i₂ (lift_fst _ _) c₁).trans (cotMap_eq_zero rfl _)
  have H₄ := (cotMap_comp p₂ i₁ (lift_snd _ _) c₂).trans (cotMap_eq_zero rfl _)
  let L := CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)
  have hL : L.IsLB := CechPic.isLB_tens hG.isLB_det hH.isLB_det
  have he : ∀ p : L.ι, IsFrame (Fin.append
      (fun i => (cotMap (fst G H) p₁).app (L.U p) (resM (omega G) inf_le_left (p.1.e i)))
      (fun j => (cotMap (snd G H) p₂).app (L.U p) (resM (omega H) inf_le_right (p.2.e j)))) := fun p =>
    GlobalTheory.TorusCot.isFrame_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
  refine LBIso.symm (lbIso_det_of_frames hL _ he fun p q => ?_).2
  refine Eq.trans ?_ (detUnit_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
    (q.1.isFrame.res inf_le_left) (q.2.isFrame.res inf_le_right) inf_le_left inf_le_right).symm
  exact congrArg₂ (· * ·) ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)
    ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)

end Prod

end GlobalTheory.HodgeProd
