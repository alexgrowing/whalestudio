import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundaryVanishingPullback
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.OpenStratumMaps

section General

variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

theorem exists_factor {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v, f v = 0 → q v = 0) : ∃ q' : σ.IntertwiningMap τ, ∀ v, q' (f v) = q v := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ w, f (s w) = w := fun w => congr($hs w)
  have key : ∀ v, q (s (f v)) = q v := fun v => by
    rw [← sub_eq_zero, ← map_sub]
    apply hq
    rw [map_sub, hs', sub_self]
  refine ⟨⟨q.toLinearMap ∘ₗ s, fun g => ?_⟩, key⟩
  ext w
  obtain ⟨v, rfl⟩ := hf w
  show q (s (σ g (f v))) = τ g (q (s (f v)))
  rw [← f.isIntertwining, key, key, q.isIntertwining]

def contraction (ρ : Representation F G V) (σ : Representation F H W) (l : W →ₗ[F] F) :
    Representation.IntertwiningMap ((extTensor ρ σ).comp (MonoidHom.inl G H)) ρ where
  toLinearMap := (TensorProduct.rid F V).toLinearMap ∘ₗ l.lTensor V
  isIntertwining' g := by
    refine TensorProduct.ext' fun v w => ?_
    show TensorProduct.rid F V (l.lTensor V (extTensor ρ σ (g, 1) (v ⊗ₜ w))) =
      ρ g (TensorProduct.rid F V (l.lTensor V (v ⊗ₜ w)))
    rw [extTensor_tmul]
    simp

theorem step {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (S T : Subrepresentation ρ) (e : (subQuot S T).Equiv σ)
    (h : ∀ f : σ.IntertwiningMap τ, ∀ w, f w = 0) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v ∈ T.toSubmodule, q v = 0) : ∀ v ∈ S.toSubmodule, q v = 0 := by
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) :=
    ⟨Submodule.mkQ _, fun g => LinearMap.ext fun v => rfl⟩
  let qS : S.toRepresentation.IntertwiningMap τ :=
    ⟨q.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => LinearMap.ext fun v => q.isIntertwining _ _ g v⟩
  obtain ⟨q', hq'⟩ := exists_factor (e.toIntertwiningMap.comp p)
    (e.toLinearEquiv.surjective.comp (Submodule.mkQ_surjective _)) qS (fun v hv => by
      have h1 : e.toLinearEquiv (Submodule.Quotient.mk v) = 0 := hv
      rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
      exact hq _ h1)
  intro v hv
  exact (hq' ⟨v, hv⟩).symm.trans (h q' _)

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.OpenStratumMaps
