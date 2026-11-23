import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem isUnit_det_trCo {B : Scheme.{0}} {M : B.Modules} {r : ℕ} {V V' : B.Opens} {f : Fin r → Γ(M, V)}
    (hf : IsFrame f) {f' : Fin r → Γ(M, V')} (hf' : IsFrame f') :
    IsUnit (Matrix.of fun b a => trCo hf f' b a).det := by
  have e : (Matrix.of fun b a => trCo hf f' b a) =
      (hf.basis (inf_le_left : V ⊓ V' ≤ V)).toMatrix (hf'.basis (inf_le_right : V ⊓ V' ≤ V')) := by
    ext b a : 2
    rw [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    rfl
  rw [e]
  have := Module.Basis.invertibleToMatrix (hf.basis (inf_le_left : V ⊓ V' ≤ V))
    (hf'.basis (inf_le_right : V ⊓ V' ≤ V'))
  exact Matrix.isUnit_det_of_invertible _

theorem flagMat_change_frame : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (V' : B.Opens) (f' : Fin r → Γ(M, V')) (hf' : IsFrame f') (K : Type) [CommRing K] (y : Sp K ⟶ Y) (x : Sp K ⟶ B) (hxx : ⊤ ≤ x ⁻¹ᵁ (V ⊓ V')) (A : Matrix (Fin r) (Fin r) K), y ≫ π = x → FlagMat hM π fl hf' y A → IsUnit (Matrix.of fun a b => TangentOrigin.evalPt x (V ⊓ V') hxx (trCo hf f' b a)).det ∧ FlagMat hM π fl hf y (A * Matrix.of fun a b => TangentOrigin.evalPt x (V ⊓ V') hxx (trCo hf f' b a)) := by
  intro B Y M r hM π fl V f hf V' f' hf' K _ y x hxx A hx hA
  subst hx
  have := hM.isQuasicoherent
  have hdet : IsUnit (Matrix.of fun a b => TangentOrigin.evalPt (y ≫ π) (V ⊓ V') hxx (trCo hf f' b a)).det := by
    have h := (isUnit_det_trCo hf hf').map (TangentOrigin.evalPt (y ≫ π) (V ⊓ V') hxx)
    rw [RingHom.map_det] at h
    rw [← Matrix.det_transpose]
    exact h
  refine ⟨hdet, by rw [Matrix.det_mul]; exact hA.1.mul hdet, fun k W hWV t hy => ?_⟩
  have hy' : ⊤ ≤ y ⁻¹ᵁ (W ⊓ π ⁻¹ᵁ V') := fun p hp => ⟨hy hp, (hxx hp).2⟩
  have h2 : W ⊓ π ⁻¹ᵁ V' ≤ π ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hWV hp.1, hp.2⟩
  obtain ⟨cf, h0, h1⟩ := hA.2 k (W ⊓ π ⁻¹ᵁ V') inf_le_right (Twist.resM _ inf_le_left t) hy'
  refine ⟨cf, h0, ?_⟩
  rw [← Matrix.vecMul_vecMul, ← h1]
  funext b
  simp only [coordAt, Matrix.vecMul, dotProduct, Matrix.of_apply]
  rw [← TangentOrigin.evalPt_res y (inf_le_left : W ⊓ π ⁻¹ᵁ V' ≤ W) hy hy', ← IsFrame.repr_resM _ hWV inf_le_left,
    FlagSec.repr_change π hf hf' _ inf_le_right h2, map_sum, Twist.app_resM]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, FlagSec.evalPt_appLE π y _ _ h2 hy' hxx, mul_comm]

end GlobalTheory.FlagCls

end
