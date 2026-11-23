import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatPt

open GlobalTheory.BCT.TrKer GlobalTheory.BCT.FinPart

theorem coord_pInf_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (e : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) e)) = v.embedding e := by
  have hv : (InfinitePlace.mk v.embedding) = v := InfinitePlace.mk_embedding v
  have h : (InfinitePlace.mk v.embedding).embedding = v.embedding := by rw [hv]
  simp only [coord, h, if_true, Pi.evalRingHom_apply]
  rw [pInf_algebraMap, hv]

theorem ratGL_mem_UA {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) :
    ratGL E n γ.1 ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  change cT (conjAd E) (ratGL E n γ.1).val * 1 * (ratGL E n γ.1).val = 1
  have hc : cT (conjAd E) (ratGL E n γ.1).val =
      (algebraMap E (Ad E)).mapMatrix (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact conjAd_algebraMap _
  have hr : (ratGL E n γ.1).val = (algebraMap E (Ad E)).mapMatrix γ.1.val := rfl
  rw [hc, hr, mul_one, ← map_mul, ← map_one (algebraMap E (Ad E)).mapMatrix, ← hγ, mul_one]

theorem ratPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  intro E _ _ _ n γ
  refine ⟨⟨ratGL E n γ.1, ratGL_mem_UA γ⟩, ⟨γ.1, rfl⟩, ?_, ?_⟩
  · set r : UA E n := ⟨ratGL E n γ.1, ratGL_mem_UA γ⟩
    have hpr : GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = ratF E n γ.1 := by
      apply Units.ext
      ext i j
      rfl
    have hi : (finPt γ).1⁻¹ * r ∈ infU E n := by
      rw [infU, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, map_inv, map_inv]
      change (pU (finPt γ))⁻¹ * GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = 1
      rw [pU_finPt, hpr, inv_mul_cancel]
    have he : r = (finPt γ).1 * (⟨_, hi⟩ : infU E n).1 := by
      simp only [mul_inv_cancel_left]
    rw [he, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (algebraMap E (Ad E) (γ.1.val i j))) = v.embedding (γ.1.val i j)
    exact coord_pInf_algebraMap v _

end GlobalTheory.BCT.RatPt
