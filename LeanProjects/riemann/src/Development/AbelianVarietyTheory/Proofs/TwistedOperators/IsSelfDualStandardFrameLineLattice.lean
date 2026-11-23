import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem isSelfDualC_span_of_norm {D : D7} (S : HSp D) (hS : S.rank = 1) (ζ : Fin S.rank → D.host.E)
    (hζ : star ζ ⬝ᵥ (HSpace.gram S *ᵥ ζ) = -1) :
    IsSelfDualC S (Submodule.span (𝓞 D.host.E) {ζ}) := by
  have hform : ∀ x y : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * HSpace.gram S i j * y j = star x ⬝ᵥ (HSpace.gram S *ᵥ y) := by
    intro x y
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  obtain ⟨i₀, hi₀⟩ : ∃ i, ζ i ≠ 0 := Function.ne_iff.mp hne
  have hall : ∀ y : Fin S.rank → D.host.E, ∃ c : D.host.E, y = c • ζ := by
    intro y
    refine ⟨y i₀ / ζ i₀, funext fun i => ?_⟩
    rw [Subsingleton.elim i i₀, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi₀]
  have hpair : ∀ a c : D.host.E, star (a • ζ) ⬝ᵥ (HSpace.gram S *ᵥ (c • ζ)) = -(star a * c) := by
    intro a c
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hζ, smul_eq_mul, smul_eq_mul]
    ring
  have hstar : ∀ a : 𝓞 D.host.E, IsIntegral ℤ (star (a : D.host.E)) := fun a =>
    (map_isIntegral_int (starRingEnd D.host.E) a.2 : )
  refine ⟨⟨Submodule.fg_span_singleton _, ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hall y
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_span_singleton_self _))
  · obtain ⟨c, rfl⟩ := hall y
    constructor
    · intro hy x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hb, hform]
      refine ⟨-(⟨_, hstar a⟩ * b), ?_⟩
      have := hpair a b
      simp only [← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E b]
      rw [this]
      rfl
    · intro h
      obtain ⟨b, hb⟩ := h ζ (Submodule.mem_span_singleton_self _)
      have h1 := hpair 1 c
      rw [one_smul, star_one, one_mul] at h1
      rw [hform, h1] at hb
      refine Submodule.mem_span_singleton.mpr ⟨-b, ?_⟩
      rw [← algebraMap_smul D.host.E (-b)]
      congr 1
      rw [map_neg]
      exact neg_eq_iff_eq_neg.mpr hb

theorem isSelfDualC_line : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  intro D T L sc G F hF
  refine isSelfDualC_span_of_norm (negSp F.Lz) F.rk (F.ζ 0) ?_
  have h1 := congrFun (congrFun G.sp.dec0.gram 0) 0
  have h2 : star (fun i => G.sp.dec0.a i 0) ⬝ᵥ (HSpace.gram (G.V (Node.core 0)) *ᵥ (fun i => G.sp.dec0.a i 0)) = 1 := by
    have h3 : antiDiagonalSignGramMatrix 1 (1 : D.host.E) 0 0 = 1 := by simp [antiDiagonalSignGramMatrix]
    rw [h3, Matrix.mul_assoc] at h1
    exact h1
  rw [← hF.zB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, F.oz.isoB] at h2
  rw [negSp_gram, neg_mulVec, dotProduct_neg]
  exact congrArg Neg.neg h2

end GlobalTheory.AscFin

end
