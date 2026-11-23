import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)

abbrev secX {Y : Scheme.{u}} (F : Y.Modules) (W : Y.Opens) (m : Γ(F, W)) :
    ((preMod Y).obj F).obj (op W) := m

abbrev secΓ {Y : Scheme.{u}} (F : Y.Modules) (W : Y.Opens) (m : ((preMod Y).obj F).obj (op W)) :
    Γ(F, W) := m

def projFun (F : X.Modules) (k : ℤ) (V : (projectiveSpace A n).Opens) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    ((preMod X).obj (F ⊗ twistingSheaf i k)).obj (op (i ⁻¹ᵁ V)) :=
  (tensorToSheaf F (twistingSheaf i k)).app (op (i ⁻¹ᵁ V))
    (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s))

variable (F : X.Modules) (k : ℤ) (V : (projectiveSpace A n).Opens)

lemma projFun_add_left (m m' : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V (m + m') s = projFun i F k V m s + projFun i F k V m' s := by
  unfold projFun
  rw [show secX F _ (m + m') = secX F _ m + secX F _ m' from rfl, TensorProduct.add_tmul]
  exact map_add _ _ _

lemma projFun_add_right (m : Γ(F, i ⁻¹ᵁ V))
    (s s' : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V m (s + s') = projFun i F k V m s + projFun i F k V m s' := by
  unfold projFun
  rw [map_add, show secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s + pullbackUnitApp i _ V s') =
    secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s) +
      secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s') from rfl, TensorProduct.tmul_add]
  exact map_add _ _ _

lemma projFun_smul_left (r : ringOn _ V) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V (secΓ F _ (appR i V r • secX F _ m)) s =
      appR i V r • projFun i F k V m s := by
  unfold projFun
  rw [show secX F _ (secΓ F _ (appR i V r • secX F _ m)) =
    appR i V r • secX F _ m from rfl, ← TensorProduct.smul_tmul']
  exact map_smul _ _ _

lemma projFun_smul_right (r : ringOn _ V) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V m (secΓ (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) _
        (r • secX (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) _ s)) =
      appR i V r • projFun i F k V m s := by
  unfold projFun
  rw [show secX (twistingSheaf i k) _ (pullbackUnitApp i _ V (secΓ (SchemeCoh.twistingSheaf
    (ProjSpace.grading A n) k) _ (r • secX (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      _ s))) = appR i V r • secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s) from
    pullbackUnitApp_smul i _ V r s, TensorProduct.tmul_smul]
  exact map_smul _ _ _

def projLin :
    ((preMod _).obj ((Scheme.Modules.pushforward i).obj F)).obj (op V) →ₗ[ringOn _ V]
      ((preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)).obj (op V) →ₗ[ringOn _ V]
      ((preMod _).obj ((Scheme.Modules.pushforward i).obj (twist i F k))).obj (op V) :=
  LinearMap.mk₂ _ (fun m s => projFun i F k V m s)
    (fun m m' s => projFun_add_left i F k V m m' s)
    (fun r m s => projFun_smul_left i F k V r m s)
    (fun m s s' => projFun_add_right i F k V m s s')
    (fun r m s => projFun_smul_right i F k V r m s)

def projPre : (preMod _).obj ((Scheme.Modules.pushforward i).obj F) ⊗
      (preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) ⟶
    (preMod _).obj ((Scheme.Modules.pushforward i).obj (twist i F k)) where
  app V := ModuleCat.ofHom
    (X := ((preMod _).obj ((Scheme.Modules.pushforward i).obj F) ⊗
      (preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)).obj V)
    (Y := ((preMod _).obj ((Scheme.Modules.pushforward i).obj (twist i F k))).obj V)
    (by exact TensorProduct.lift (projLin i F k V.unop))
  naturality {V V'} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m s
    have e1 := pullbackUnitApp_res i (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) f.unop s
    have e2 := PresheafOfModules.naturality_apply (tensorToSheaf F (twistingSheaf i k))
      ((Opens.map i.base).map f.unop).op
      (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ (pullbackUnitApp i _ V.unop s))
    change projFun i F k V'.unop (F.presheaf.map ((Opens.map i.base).map f.unop).op m)
        ((SchemeCoh.twistingSheaf (ProjSpace.grading A n) k).presheaf.map f.unop.op s) =
      ((preMod X).obj (F ⊗ twistingSheaf i k)).map ((Opens.map i.base).map f.unop).op
        (projFun i F k V.unop m s)
    unfold projFun
    rw [e1]
    exact e2

def projectionMap :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ⟶
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  tensorLift (projPre i F k)

lemma projectionMap_tensorBasisMap (j : Fin (n + 1)) {V : (projectiveSpace A n).Opens}
    (hV : V ≤ ProjSpace.stdOpen A n j) (m : Γ((Scheme.Modules.pushforward i).obj F, V)) :
    (projectionMap i F k).app V (tensorBasisMap ((Scheme.Modules.pushforward i).obj F)
        (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
        (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m) =
      tensorBasisMap F (twistingSheaf i k)
        (pullbackUnitApp i _ (ProjSpace.stdOpen A n j)
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
        ((Opens.map i.base).monotone hV) (secΓ F _ m) := by
  have h := congrArg (fun φ => (PresheafOfModules.Hom.app φ (op V)).hom
      ((show ((preMod _).obj ((Scheme.Modules.pushforward i).obj F)).obj (op V) from m) ⊗ₜ
        resM ((preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)) hV
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) :
        ((preMod _).obj ((Scheme.Modules.pushforward i).obj F) ⊗
          (preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)).obj (op V)))
    (tensorToSheaf_tensorLift (projPre i F k))
  refine h.trans ?_
  change projFun i F k V m (resM _ hV (ProjTwist.upow (ProjSpace.grading A n)
    (ProjSpace.X_mem j) k)) = _
  unfold projFun
  have e := pullbackUnitApp_res i (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) (homOfLE hV)
    (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k)
  exact congrArg (fun y => (tensorToSheaf F (twistingSheaf i k)).app (op (i ⁻¹ᵁ V))
    (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ y)) e

instance isIso_projectionMap : IsIso (projectionMap i F k) := by
  apply isIso_of_locally_bijective
  intro x
  obtain ⟨j, hj⟩ : ∃ j, x ∈ ProjSpace.stdOpen A n j :=
    Opens.mem_iSup.1 (by rw [ProjSpace.iSup_stdOpen]; trivial)
  refine ⟨ProjSpace.stdOpen A n j, hj, fun V hV => ?_⟩
  have hb₁ := tensorBasisMap_bijective (M := (Scheme.Modules.pushforward i).obj F)
    (ProjTwist.isBasisOn_upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV
  have hb₂ := tensorBasisMap_bijective (M := F)
    (isBasisOn_pullbackUnitApp i
      (ProjTwist.isBasisOn_upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
    ((Opens.map i.base).monotone hV)
  have comm : (fun m => (projectionMap i F k).app V (tensorBasisMap
      ((Scheme.Modules.pushforward i).obj F) (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m)) =
      (fun m => tensorBasisMap F (twistingSheaf i k)
        (pullbackUnitApp i _ (ProjSpace.stdOpen A n j)
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
        ((Opens.map i.base).monotone hV) (secΓ F _ m)) :=
    funext fun m => projectionMap_tensorBasisMap i F k j hV m
  have h2 : Function.Bijective (fun m => (projectionMap i F k).app V (tensorBasisMap
      ((Scheme.Modules.pushforward i).obj F) (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m)) := by
    rw [comm]
    exact hb₂
  exact (Function.Bijective.of_comp_iff _ hb₁).1 h2

def pushforwardTwistIso' :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ≅
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  asIso (projectionMap i F k)

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
