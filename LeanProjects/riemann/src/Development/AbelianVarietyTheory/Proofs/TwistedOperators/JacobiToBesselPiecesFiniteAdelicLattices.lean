import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Transfer

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D n k) :
    MxAt (fun _ => True) (x ⬝ M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D k m) :
    MxAt (fun _ => True) (M ⬝ x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem finLat_comap {m n m' n' : ℕ} {Γ : AddSubgroup (Mx D m' n')} (hΓ : FinLat Γ) (f : Mx D m n →+ Mx D m' n')
    (g : Mx D m' n' → Mx D m n) (hf : Continuous f) (hg : Continuous g) (hgf : ∀ a, g (f a) = a)
    (hfM : ∀ a, MxAt (fun _ => True) a → MxAt (fun _ => True) (f a))
    (hgM : ∀ b, MxAt (fun _ => True) b → MxAt (fun _ => True) (g b)) : FinLat (Γ.comap f) where
  fin a ha := hgf a ▸ hgM _ (hΓ.fin _ ha)
  cpt := by
    haveI : T2Space (Mx D m' n') := (GlobalTheory.MixModel.lattice_Mx D m' n').2.2.2.1
    have hc : IsClosed ((Γ.comap f : AddSubgroup _) : Set (Mx D m n)) := hΓ.cpt.isClosed.preimage hf
    refine (hΓ.cpt.image hg).of_isClosed_subset hc ?_
    intro a ha
    exact ⟨f a, ha, hgf a⟩
  opn := by
    obtain ⟨U, hU, h0, hUΓ⟩ := hΓ.opn
    exact ⟨f ⁻¹' U, hU.preimage hf, by simpa using h0, fun a ha hA => hUΓ _ ha (hfM a hA)⟩

end Transfer

theorem pcFB_fin : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧
      ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  intro D hOff T L μ0 hL sc G W M hM F hF σ h h'
  have hlat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF).1 (2 * σ + 2) (by omega)
  have hRow : FinLat (latRow G (2 * σ + 2)) := hlat.1
  have hBig : FinLat (latBig G (2 * σ + 2)) := hlat.2.2.1
  set dV := F.dJ (σ + 1) h
  set dW := F.dB σ h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finLat_comap hRow (dV.extX _) (fun w => w ⬝ dV.jX) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
      (fun a => by simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one])
      (fun a ha => mxAt_mul_right ha _) (fun b hb => mxAt_mul_right hb _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incX _)) (fun w => dW.pX ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pX, HypDec.pX_jX, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incY _)) (fun w => dW.pY ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pY, HypDec.pY_jY, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · intro u hu
    have h1 := hRow.fin _ hu
    have h2 : dW.p0 ⬝ (((dV.ext0 _).comp (dW.inc0 _)) u ⬝ dV.j0) = u := by
      simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.p0, Matrix.one_mul]
    rw [← h2]
    exact mxAt_mul_left (mxAt_mul_right h1 _) _

end GlobalTheory.AscFin
