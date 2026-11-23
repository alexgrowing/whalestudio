import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

theorem form_mulVec_mulVec {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (J γ : Matrix (Fin m) (Fin m) E)
    (x y : Fin m → E) :
    GlobalTheory.SgAlg.form σ J (γ *ᵥ x) (γ *ᵥ y) = GlobalTheory.SgAlg.form σ (GlobalTheory.SgAlg.cT σ γ * J * γ) x y := by
  have h : (fun i => σ ((γ *ᵥ y) i)) = (fun i => σ (y i)) ᵥ* GlobalTheory.SgAlg.cT σ γ := by
    funext i
    simp [GlobalTheory.SgAlg.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  simp only [GlobalTheory.SgAlg.form]
  rw [h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem form_single_single {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (M : Matrix (Fin m) (Fin m) E)
    (i j : Fin m) : GlobalTheory.SgAlg.form σ M (Pi.single j 1) (Pi.single i 1) = M i j := by
  simp [GlobalTheory.SgAlg.form, dotProduct, Pi.single_apply, Matrix.mulVec_single]

theorem isUn_iff_mem_isom {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) :
    GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  constructor
  · intro hU
    change ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y
    intro x y
    rw [← vecOf_crdH X x, ← vecOf_crdH X y, n_vecOf hγ, n_vecOf hγ, hT_vecOf, hT_vecOf,
      form_mulVec_mulVec, hU]
  · intro hn
    have hn' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
    ext i j
    rw [← form_single_single _ (GlobalTheory.SgAlg.cT _ γ * Jc X * γ) i j, ← form_mulVec_mulVec,
      ← hT_vecOf X, ← n_vecOf hγ, ← n_vecOf hγ, hn', hT_vecOf, form_single_single]

end GlobalTheory.CovDomGrp
