import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepTensor

theorem extTensor_left {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (k : G) :
    extTensor ρ σ (k, 1) = TensorProduct.map (ρ k) LinearMap.id :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem extTensor_right {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (h : H) :
    extTensor ρ σ (1, h) = TensorProduct.map LinearMap.id (σ h) :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem contr_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (l : Module.Dual ℂ W) (v : V ⊗[ℂ] W) :
    A (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
      TensorProduct.rid ℂ V (LinearMap.lTensor V l (TensorProduct.map A LinearMap.id v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem contr_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : Module.End ℂ W) (l : Module.Dual ℂ V) (v : V ⊗[ℂ] W) :
    B (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
      TensorProduct.lid ℂ W (LinearMap.rTensor W l (TensorProduct.map LinearMap.id B v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    have := h k k.2
    show ρ (k : G) v = ((1 : K →* ℂˣ) k : ℂ) • v
    simpa using this

theorem contrFix : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  intro G H V W _ _ _ _ _ _ ρ σ K L v hv
  have hv' := mem_fixed_iff'.1 hv
  refine ⟨fun l => mem_fixed_iff'.2 fun k hk => ?_, fun l => mem_fixed_iff'.2 fun h hh => ?_⟩
  · have h1 := hv' (k, 1) ⟨hk, L.one_mem⟩
    rw [extTensor_left] at h1
    rw [contr_left, h1]
  · have h1 := hv' (1, h) ⟨K.one_mem, hh⟩
    rw [extTensor_right] at h1
    rw [contr_right, h1]

end GlobalTheory.CompanionTheory.RepTensor
