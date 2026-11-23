import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7} (W : HSp D)

theorem exists_gqMat (γ : GQ W) : ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat c = mt W γ :=
  mem_ratMx.1 ((mem_GQ_iff W γ).1 γ.2)

def gqMat (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_gqMat W γ)

theorem rat_gqMat (γ : GQ W) : rat (gqMat W γ) = mt W γ := Classical.choose_spec (exists_gqMat W γ)

theorem gqMat_map (γ : GQ W) : (gqMat W γ).map (incA D) = mt W γ := rat_gqMat W γ

theorem gqMat_mul (γ δ : GQ W) : gqMat W (γ * δ) = gqMat W γ * gqMat W δ :=
  rat_injective (by rw [rat_mul, rat_gqMat, rat_gqMat, rat_gqMat]; rfl)

theorem gqMat_one : gqMat W 1 = 1 := rat_injective (by rw [rat_gqMat, rat_one]; rfl)

theorem gqMat_inv_mul (γ : GQ W) : gqMat W γ⁻¹ * gqMat W γ = 1 := by
  rw [← gqMat_mul, inv_mul_cancel, gqMat_one]

theorem gqMat_mul_inv (γ : GQ W) : gqMat W γ * gqMat W γ⁻¹ = 1 := by
  rw [← gqMat_mul, mul_inv_cancel, gqMat_one]

theorem gqMat_unitary (γ : GQ W) : (gqMat W γ)ᴴ * W.gram * gqMat W γ = W.gram := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_gqMat]
  exact mt_rel W γ

def actEquiv (γ : GQ W) :
    ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E] ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearEquiv.prodCongr
    (LinearEquiv.ofLinear (Matrix.toLin' (gqMat W γ)) (Matrix.toLin' (gqMat W γ⁻¹))
      (by rw [← Matrix.toLin'_mul, gqMat_mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, gqMat_inv_mul, Matrix.toLin'_one]))
    (LinearEquiv.refl _ _)

theorem actEquiv_apply (γ : GQ W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    actEquiv W γ y = (gqMat W γ *ᵥ y.1, y.2) := rfl

theorem isotropic_mulVec (γ : GQ W) (x x' : Fin W.rank → D.host.E) :
    star (gqMat W γ *ᵥ x) ⬝ᵥ W.gram *ᵥ (gqMat W γ *ᵥ x') = star x ⬝ᵥ W.gram *ᵥ x' := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, gqMat_unitary]

def lagAct (γ : GQ W) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _), by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [LinearEquiv.coe_coe, actEquiv_apply]
    rw [isotropic_mulVec]
    exact Y.2.2 y hy y' hy'⟩

theorem mem_lagAct (γ : GQ W) (Y : Lag W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    y ∈ (lagAct W γ Y).1 ↔ (gqMat W γ⁻¹ *ᵥ y.1, y.2) ∈ Y.1 := by
  show y ∈ Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem lagAct_one (Y : Lag W) : lagAct W 1 Y = Y := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, inv_one, gqMat_one, Matrix.one_mulVec]

theorem lagAct_mul (γ δ : GQ W) (Y : Lag W) : lagAct W (γ * δ) Y = lagAct W γ (lagAct W δ Y) := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, mem_lagAct, mem_lagAct, _root_.mul_inv_rev, gqMat_mul]
  simp only [Matrix.mulVec_mulVec]

theorem isLagFrame_lagAct (γ : GQ W) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    IsLagFrame W (lagAct W γ Y) (gqMat W γ * C.1, C.2) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (actEquiv W γ).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

abbrev NGLag (W : HSp D) : Type := {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}

theorem lagAct_ne_bot (γ : GQ W) (Y : Lag W) (h : Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥) :
    (lagAct W γ Y).1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 h
  refine (Submodule.ne_bot_iff _).2 ⟨gqMat W γ *ᵥ x, ?_, ?_⟩
  · rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lagAct, Matrix.mulVec_mulVec, gqMat_inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h0
    apply hx0
    have := congrArg (fun v => gqMat W γ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, gqMat_inv_mul] using this

def ngAct (γ : GQ W) (Y : NGLag W) : NGLag W := ⟨lagAct W γ Y.1, lagAct_ne_bot W γ Y.1 Y.2⟩

theorem ngAct_one (Y : NGLag W) : ngAct W 1 Y = Y := Subtype.ext (lagAct_one W Y.1)

theorem ngAct_mul (γ δ : GQ W) (Y : NGLag W) : ngAct W (γ * δ) Y = ngAct W γ (ngAct W δ Y) :=
  Subtype.ext (lagAct_mul W γ δ Y.1)

end GlobalTheory.RallisCusp

end
