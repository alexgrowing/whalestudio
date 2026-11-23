import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem conjTranspose_gram_mul_apply {D : D7} {n s t : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E)
    (A : Matrix (Fin n) (Fin s) D.host.E) (B : Matrix (Fin n) (Fin t) D.host.E) (a : Fin s) (c : Fin t) :
    (Aᴴ * G * B) a c = star (fun k => A k a) ⬝ᵥ G.mulVec (fun k => B k c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem exists_isoFrame_comap_inl : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
    ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  intro D W Y hY
  set I₁ := Y.1.comap (LinearMap.inl D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)) with hI₁
  have hpos : 0 < Module.finrank D.host.E I₁ :=
    Nat.pos_of_ne_zero fun h => hY (Submodule.finrank_eq_zero.mp h)
  let b := Module.finBasisOfFinrankEq D.host.E I₁ rfl
  have hsp : Submodule.span D.host.E (Set.range (I₁.subtype ∘ b)) = I₁ := by
    have h := congrArg (Submodule.map I₁.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  let I : Matrix (Fin W.rank) (Fin (Module.finrank D.host.E I₁)) D.host.E :=
    Matrix.of fun a j => (b j : Fin W.rank → D.host.E) a
  have hT : I.transpose = I₁.subtype ∘ b := by
    funext j a
    rfl
  refine ⟨_, I, ⟨hpos, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact b.linearIndependent.map' I₁.subtype (Submodule.ker_subtype I₁)
  · rw [GlobalTheory.MixModel.cT_sig]
    refine Matrix.ext fun a c => ?_
    rw [conjTranspose_gram_mul_apply, Matrix.zero_apply]
    have ha : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b a : Fin W.rank → D.host.E) ∈ Y.1 := (b a).2
    have hc : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b c : Fin W.rank → D.host.E) ∈ Y.1 := (b c).2
    have h := Y.2.2 _ ha _ hc
    simp only [LinearMap.inl_apply, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h
    exact h
  · rw [hT]
    exact hsp

end GlobalTheory.RawLift
