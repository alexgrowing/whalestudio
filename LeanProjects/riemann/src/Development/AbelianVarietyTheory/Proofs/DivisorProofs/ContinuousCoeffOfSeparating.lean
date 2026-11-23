import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

namespace GlobalTheory.ContinuousRepresentationCoefficients

theorem continuous_coeff_of_separating {X V ι : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (L : ι → V →ₗ[ℂ] ℂ)
    (hL : ∀ v, (∀ i, L i v = 0) → v = 0) (f : X → V) (hf : ∀ i, Continuous fun x => L i (f x))
    (ℓ : Module.Dual ℂ V) : Continuous fun x => ℓ (f x) := by
  have hmem : ℓ ∈ Submodule.span ℂ (Set.range L) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have h0 : v = 0 := hL v fun i => by
      simpa using (Submodule.mem_iInf _).1 hv i
    simp [h0]
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => simpa using continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact (continuous_const (y := c)).mul hx

theorem continuous_translate {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (φ : GlobalTheory.CuspRep.Sm E a) (g : GlobalTheory.CuspRep.GA E a) :
    Continuous fun k : GlobalTheory.CuspRep.Kinf E a =>
      ((GlobalTheory.CuspRep.cptRep E a k φ : GlobalTheory.CuspRep.Sm E a) : GlobalTheory.CuspRep.GA E a → ℂ) g := by
  have h1 : ContinuousOn (GlobalTheory.CuspRep.chart φ.1 g) (GlobalTheory.CuspRep.invSet E a) :=
    (φ.2 g).continuousOn
  have hu : ∀ k : GlobalTheory.CuspRep.Kinf E a,
      IsUnit (Matrix.of (k.1 : GlobalTheory.CuspRep.Lie E a)) := fun k => (Unitary.toUnits k).isUnit
  have h2 : Continuous fun k : GlobalTheory.CuspRep.Kinf E a => (k.1 : GlobalTheory.CuspRep.Lie E a) :=
    continuous_subtype_val
  have h3 := h1.comp_continuous h2 hu
  refine h3.congr fun k => ?_
  have h4 : (hu k).unit = Unitary.toUnits k := Units.ext rfl
  show GlobalTheory.CuspRep.chart φ.1 g (k.1 : GlobalTheory.CuspRep.Lie E a) = _
  unfold GlobalTheory.CuspRep.chart
  rw [dif_pos (hu k), h4]
  rfl

theorem isContRep_sub {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E a))
    (hW : ∀ (k : GlobalTheory.CuspRep.Kinf E a), ∀ w ∈ W, GlobalTheory.CuspRep.cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] :
    GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (GlobalTheory.CuspRep.cptRep E a) W hW) := by
  intro ℓ w
  refine continuous_coeff_of_separating
    (fun g : GlobalTheory.CuspRep.GA E a =>
      (LinearMap.proj g : (GlobalTheory.CuspRep.GA E a → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (GlobalTheory.CuspRep.Sm E a).subtype ∘ₗ W.subtype) ?_ _ ?_ ℓ
  · intro v hv
    exact Subtype.ext (Subtype.ext (funext hv))
  · intro g
    exact continuous_translate w.1 g

end GlobalTheory.ContinuousRepresentationCoefficients
