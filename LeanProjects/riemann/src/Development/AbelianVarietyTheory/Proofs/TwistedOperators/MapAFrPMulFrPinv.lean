import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frPinv_mul_frP : frPinv S b * frP S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

def frPinvGL : GL (Fin S.rank) (Lev.EAf D) :=
  ⟨(frPinv S b).map (eToEAf D), (frP S b).map (eToEAf D),
    by rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _),
    by rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)⟩

theorem frPinvGL_inv_val : (frPinvGL S b)⁻¹.val = (frP S b).map (eToEAf D) := rfl

def reWi (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem mapA_frPinv_mul_frP : (frPinv S b).map (incA D) * (frP S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_frP_mul_map_frPinv : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem reW_reWi (x : WO S T) : reW S T b (reWi S T b x) = x := by
  unfold reW reWi
  rw [Matrix.mul_assoc, map_frP_mul_map_frPinv, Matrix.mul_one]

theorem reWi_reW (x : WO (reS S b) T) : reWi S T b (reW S T b x) = x := by
  have h := Matrix.mul_assoc (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D))
  rw [mapA_frPinv_mul_frP, Matrix.mul_one] at h
  exact h

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (reW_add S T b)

theorem reW_nsmul (k : ℕ) (x : WO (reS S b) T) : reW S T b (k • x) = k • reW S T b x :=
  map_nsmul (reWHom S T b) k x

theorem reW_bijective : Function.Bijective (reW S T b) :=
  Function.bijective_iff_has_inverse.2 ⟨reWi S T b, reWi_reW S T b, reW_reWi S T b⟩

theorem isHalf_reW_iff (e : AE D) (x : WO (reS S b) T) : IsHalf e (reW S T b x) ↔ IsHalf e x := by
  have key : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) (AE D)),
      IsHalf e M → IsHalf e (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) M N) := by
    intro M N h i j
    simp only [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, h i l]
  constructor
  · intro h
    have h2 := key _ ((frP S b).map (incA D)) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · intro h
    exact key x _ h

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ)
    (hs : ∀ x y, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T u (reF S T b f) = reF S T b (heisO ψ S T (reW S T b u) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, hs, reW_add]

end GlobalTheory.AdSpan.ReVec

end
