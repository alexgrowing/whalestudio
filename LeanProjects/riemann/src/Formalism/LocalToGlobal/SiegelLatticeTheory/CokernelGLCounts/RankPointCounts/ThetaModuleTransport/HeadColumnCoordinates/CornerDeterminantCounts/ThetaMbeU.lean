import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUL

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThetaMbeU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = Nat.card (IsoMbe Z₁.Z Z₂.Z)

def MbeU (M : Model F E) (r : ℕ) : Prop :=
  ∀ (Z₁ Z₂ : M.Mat (r + 1)) (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
    (∀ a b : Fin r, Y₁.Z a b = Z₁.Z a.castSucc b.castSucc ∧ Y₂.Z a b = Z₂.Z a.castSucc b.castSucc) →
    (∀ a : Fin r, be₁ a = Z₁.Z a.castSucc (Fin.last r) ∧ be₂ a = Z₂.Z a.castSucc (Fin.last r) ∧
      al₁ a = Z₁.Z (Fin.last r) a.castSucc ∧ al₂ a = Z₂.Z (Fin.last r) a.castSucc) →
    headDet M Z₁.Z * (Z₂.Z.map M.R.subtype).det = headDet M Z₂.Z * (Z₁.Z.map M.R.subtype).det →
    Nat.card (IsoMbe Z₁.Z Z₂.Z) = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂

def CornerU (M : Model F E) (r : ℕ) : Prop :=
  ∀ (Z₁ : M.Mat (r + 1)) (Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y₁ Y₂ : M.Mat r)
    (be₁ be₂ al₁ al₂ : Fin r → M.R),
    (∀ a b : Fin r, Y₁.Z a b = Z₁.Z a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = Zh₂ a.castSucc b.castSucc) →
    (∀ a : Fin r, be₁ a = Z₁.Z a.castSucc (Fin.last r) ∧ (be₂ a : E) = Zh₂ a.castSucc (Fin.last r) ∧
      al₁ a = Z₁.Z (Fin.last r) a.castSucc ∧ (al₂ a : E) = Zh₂ (Fin.last r) a.castSucc) →
    headDet M Z₁.Z * Zh₂.det = (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * (Z₁.Z.map M.R.subtype).det →
    Nonempty {φ : M.Cok Y₁ ≃ₗ[M.R] M.Cok Y₂ // φ (Submodule.Quotient.mk be₁) = Submodule.Quotient.mk be₂ ∧
      ∀ v, M.linQ Y₂ al₂ (φ v) = M.linQ Y₁ al₁ v} →
    Zh₂ (Fin.last r) (Fin.last r) ∈ M.R

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
