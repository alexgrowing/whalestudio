import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

noncomputable section

namespace GlobalTheory.LineFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def frameEquiv {N m : ℕ} (hr : N = m + 2) : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ Fin N :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def frameMat {v : Pl F} (t : E →ₐ[F] Fv F v) {N m : ℕ} (H : Plane E N m) (hr : N = m + 2) :
    Matrix (Fin N) (Fin N) (Fv F v) :=
  ((GlobalTheory.JacGeom.frame H.x H.ι H.y).map t).submatrix id (frameEquiv hr).symm

open Classical in

def frameGL {v : Pl F} (t : E →ₐ[F] Fv F v) {N m : ℕ} (H : Plane E N m) (hr : N = m + 2) : GL (Fin N) (Fv F v) :=
  if h : IsUnit (frameMat t H hr) then h.unit else 1

def locY {v : Pl F} (t : E →ₐ[F] Fv F v) : ((splitPrime t).adicCompletion E)ˣ →* (Fv F v)ˣ :=
  Units.map (GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).symm.toMonoidHom

theorem frameEquiv_inl {N m : ℕ} (hr : N = m + 2) (i : Fin 1) : ((frameEquiv hr (.inl i)) : ℕ) = 0 := by
  simp [frameEquiv, Fin.fin_one_eq_zero i]

theorem frameEquiv_mid {N m : ℕ} (hr : N = m + 2) (j : Fin m) : ((frameEquiv hr (.inr (.inl j))) : ℕ) = j + 1 := by
  simp [frameEquiv]; omega

theorem frameEquiv_inr {N m : ℕ} (hr : N = m + 2) (i : Fin 1) : ((frameEquiv hr (.inr (.inr i))) : ℕ) = m + 1 := by
  simp [frameEquiv, Fin.fin_one_eq_zero i]; omega

theorem frameGL_val {v : Pl F} (t : E →ₐ[F] Fv F v) {N m : ℕ} (H : Plane E N m) (hr : N = m + 2)
    (h : IsUnit (frameMat t H hr)) : ((frameGL t H hr : GL (Fin N) (Fv F v)) : Matrix (Fin N) (Fin N) (Fv F v)) =
      frameMat t H hr := by
  rw [frameGL, dif_pos h]; rfl

end GlobalTheory.LineFrame

namespace GlobalTheory.LineFrame
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem complMap_locY {v : Pl F} (t : E →ₐ[F] Fv F v) (x : ((splitPrime t).adicCompletion E)ˣ) :
    Units.map (GlobalTheory.LFun.complMap (splitPrime_under t)).toMonoidHom (locY t x) = x := by
  refine Units.ext ?_
  exact (GlobalTheory.LFun.SplitTie.complEquiv t (splitPrime_under t)).apply_symm_apply (x : (splitPrime t).adicCompletion E)

theorem locIdele_eq_idl {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (x : ((splitPrime t).adicCompletion E)ˣ) : locIdele F (splitPrime t) x = GlobalTheory.JacGeom.idl h t (locY t x, 1) := by
  have e := GlobalTheory.ChrLocal.eq_locIdele_splitPrime h t (GlobalTheory.JacGeom.idl h t (locY t x, 1)) (GlobalTheory.JacGeom.at_idl h t _ _)
    (by rw [GlobalTheory.JacGeom.piW_comp_idl]; rfl)
  have hp : Units.map (piW t).toMonoidHom (GlobalTheory.JacGeom.idl h t (locY t x, 1)) = locY t x :=
    Units.ext (GlobalTheory.JacGeom.piW_idl h t _ _)
  rw [e, hp, complMap_locY]

theorem twAbs_locIdele {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (χ : Chr F E) (s : ℝ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (x : ((splitPrime t).adicCompletion E)ˣ) :
    ((GlobalTheory.CtTyp.twAbs χ s (locIdele F (splitPrime t) x) : ℂˣ) : ℂ) =
      (chrW χ t (locY t x) : ℂ) * (absPow (Fv F v) (s : ℂ) (locY t x) : ℂ) := by
  have hc : (chrW χ t (locY t x) : ℂ) = (χ (locIdele F (splitPrime t) x) : ℂ) := by
    change ((Circle.toUnits (χ (locIdele F (splitPrime t) (Units.map _ (locY t x))))) : ℂ) = _
    rw [complMap_locY]
    rfl
  have ha : (absE F E (locIdele F (splitPrime t) x) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (locY t x) := by
    rw [locIdele_eq_idl h t x, GlobalTheory.JacGeom.absE_idl]
    simp [GlobalTheory.SplitWeil.nabs]
  rw [hc]
  change (χ _ : ℂ) * (((absE F E _ : ℝ) ^ s : ℝ) : ℂ) = _
  rw [ha]
  congr 1
  change _ = ((GlobalTheory.SplitWeil.nabs (Fv F v) (locY t x) : ℝ) : ℂ) ^ (s : ℂ)
  rw [Complex.ofReal_cpow (by simp [GlobalTheory.SplitWeil.nabs])]

end GlobalTheory.LineFrame
