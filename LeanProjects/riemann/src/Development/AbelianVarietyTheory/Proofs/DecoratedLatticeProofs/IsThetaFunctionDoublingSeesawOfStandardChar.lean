import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)

noncomputable section

namespace GlobalTheory.Core.Rk.DeltaTheta

variable {D : D7}

def fstH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun x := -resR A B x
  map_zero' := neg_zero
  map_add' x y := neg_add (resR A B x) (resR A B y)

theorem continuous_fstH (A B : HSp D) : Continuous (fstH A B) :=
  continuous_matrix fun i _ => continuous_id.matrix_elem i _

theorem continuous_sndH (A B : HSp D) : Continuous (sndH A B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  have h : Continuous (resR A B) := continuous_matrix fun i _ => continuous_id.matrix_elem i _
  exact h.neg

theorem map_fstH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (fstH A B u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h i) (finSumFinEquiv (Sum.inl j))

theorem map_sndH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (sndH A B u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u i (finSumFinEquiv (Sum.inr j))) = 0 := congrFun (congrFun h i) (finSumFinEquiv (Sum.inr j))
    change φ (-(u i (finSumFinEquiv (Sum.inr j)))) = 0
    rw [map_neg, e, neg_zero]

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (fstH A B x) (fstH A B y) - hO A B (sndH A B x) (sndH A B y) := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, fstH, sndH, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y =
      symplOH A B (fstH A B x) (fstH A B y) - symplOH A B (sndH A B x) (sndH A B y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, hO_dbl, map_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem isThetaFunO_delta {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) {A B : HSp D} {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) : IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  have hd : delta A B f₁ f₂ = fun w => f₁ (fstH A B w) * conj (f₂ (sndH A B w)) := rfl
  rw [hd]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e₁ : fstH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => γ i (finSumFinEquiv (Sum.inl j))) := rfl
    have e₂ : sndH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => -γ i (finSumFinEquiv (Sum.inr j))) :=
      Matrix.ext fun i j => (map_neg (incA D) _).symm
    rw [map_add, map_add, symplOH_dbl, e₁, e₂, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (fstH A B) ⊓ U₂.comap (sndH A B),
      (hU₁.preimage (continuous_fstH A B)).inter (hU₂.preimage (continuous_sndH A B)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_fstH _ _ _ h0)) (fstH A B w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ _ _ h0)) (sndH A B w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOH_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add, map_add, map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_fstH A B)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH A B)))
  · simp only [map_add]
    exact (h₁.smooth k ((fstH A B).comp L) ((continuous_fstH A B).comp hL) (fun t => map_fstH _ _ _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH A B).comp L) ((continuous_sndH A B).comp hL)
        (fun t => map_sndH _ _ _ (h0 t)) _))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) :=
  fun _ _ _ _ hψ _ _ h₁ h₂ => isThetaFunO_delta hψ.1.2.1 h₁ h₂

end GlobalTheory.Core.Rk.DeltaTheta

end
