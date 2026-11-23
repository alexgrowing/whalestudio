import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionFunctionIncZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjCore

variable {D : D7}

theorem rat_entry' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mul_mem_hatMx {m n : ℕ} {ΛS : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT) (I : Ideal (𝓞 D.host.E)) {z : Mx D m n} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D m m) ⬝ z ∈ hatMx (I • homLat ΛS ΛT) := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X ∈ I • homLat ΛS ΛT := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · rw [Matrix.mul_smul]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec]
      exact hM _ (hY _ hy)
    · rw [Matrix.mul_add]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, TensorProduct.tmul_sum, rat_entry',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem proj_mem_latCore : OnStd fun {D} _ _ _ {G} _ F => ∀ u ∈ latCore G 0, F.oz.jA ⬝ (F.oz.pA ⬝ u) ∈ latCore G 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF u hu
  have hz := hF.zA
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    have hp := G.sp.dec0.perp
    rw [show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) =
        (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ from Matrix.ext fun _ _ => rfl, ← hz] at hp
    rw [OrthDec.qA, Matrix.mul_assoc, hp, Matrix.mul_zero]
  have hmap : ∀ x ∈ G.Λ (.core 0), (F.oz.iA * F.oz.qA) *ᵥ x ∈ G.Λ (.core 0) := by
    intro x hx
    have hx' : x ∈ G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := by rw [← G.sp.lat0]; exact hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨y, hy, 0, fun _ => Submodule.zero_mem _, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_zero, add_zero, ← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, F.oz.qA_iA, Matrix.mul_one, Matrix.mul_assoc, hqa, Matrix.mul_zero, Matrix.zero_mulVec, add_zero]
  have he : F.oz.jA ⬝ (F.oz.pA ⬝ u) = (rat (F.oz.iA * F.oz.qA) : Mx D _ _) ⬝ u := by
    rw [rat_mul, ← Matrix.mul_assoc]; rfl
  rw [he]
  refine ⟨?_, fun e he' => ?_⟩
  · exact GlobalTheory.OverTgt.mul_mem_latO (LT := G.Λ (.core 0)) (LT' := G.Λ (.core 0)) _
      (fun y hy => GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ hmap hy) hu.1
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx _ hmap _ (hu.2 e he')

end GlobalTheory.ProjCore
