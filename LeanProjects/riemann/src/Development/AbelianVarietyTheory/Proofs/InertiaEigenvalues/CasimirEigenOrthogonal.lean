import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrixStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

open Classical in

def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

def adjAlg : Subalgebra ℂ (Module.End ℂ (Sm E N)) where
  carrier := {z | (∀ φ ∈ W, z φ ∈ W) ∧ (∀ φ ∈ J, z φ ∈ J) ∧ ∃ z' : Module.End ℂ (Sm E N),
    (∀ φ ∈ W, z' φ ∈ W) ∧ (∀ φ ∈ J, z' φ ∈ J) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (z φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (z' ψ))}
  mul_mem' := by
    rintro x y ⟨hx, hxJ, x', hx', hx'J, ex⟩ ⟨hy, hyJ, y', hy', hy'J, ey⟩
    refine ⟨fun φ hφ => hx _ (hy φ hφ), fun φ hφ => hxJ _ (hyJ φ hφ), y' * x', fun φ hφ => hy' _ (hx' φ hφ),
      fun φ hφ => hy'J _ (hx'J φ hφ), fun φ hφ ψ hψ => ?_⟩
    exact (ex _ (hy φ hφ) ψ hψ).trans (ey φ hφ _ (hx' ψ hψ))
  add_mem' := by
    rintro x y ⟨hx, hxJ, x', hx', hx'J, ex⟩ ⟨hy, hyJ, y', hy', hy'J, ey⟩
    refine ⟨fun φ hφ => W.add_mem (hx φ hφ) (hy φ hφ), fun φ hφ => J.add_mem (hxJ φ hφ) (hyJ φ hφ), x' + y',
      fun φ hφ => W.add_mem (hx' φ hφ) (hy' φ hφ), fun φ hφ => J.add_mem (hx'J φ hφ) (hy'J φ hφ), fun φ hφ ψ hψ => ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, cls_add h (hx φ hφ) (hy φ hφ), cls_add h (hx' ψ hψ) (hy' ψ hψ),
      inner_add_left, inner_add_right, ex φ hφ ψ hψ, ey φ hφ ψ hψ]
  algebraMap_mem' := by
    intro c
    refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, algebraMap ℂ _ (starRingEnd ℂ c), fun φ hφ => ?_, fun φ hφ => ?_,
      fun φ hφ ψ hψ => ?_⟩
    · rw [Module.algebraMap_end_apply]; exact W.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact J.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact W.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact J.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, cls_smul h _ hφ, cls_smul h _ hψ,
        inner_smul_left, inner_smul_right]

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
