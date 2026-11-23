import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspidalFormsGLTotallyComplexStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory Topology

noncomputable section

namespace GlobalTheory.HCFCusp

theorem finiteDimensional_cuspSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  intro E _ _ _ a L hL W _ χ N ν _ α _ _
  have hopen : ∀ φ : Sm E a, (∀ k ∈ L, finRep E a k φ = φ) → IsOpen {k | finRep E a k φ = φ} := by
    intro φ hφ
    rw [isOpen_iff_forall_mem_open]
    intro k hk
    refine ⟨(k * ·) '' (L : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hL, ⟨1, L.one_mem, mul_one k⟩⟩
    rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, hφ l hl]
    exact hk
  refine GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex E a L hL W ‹_› {χ} (Set.finite_singleton χ) N _
    (Submodule.span_mono fun φ hφ => hφ.1) ?_
  intro φ hφ
  have P : (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsCuspidal φ.1 := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨hx.1.2.1, hx.1.1.left, hx.2⟩
    | zero =>
      refine ⟨fun k _ => map_zero _, fun _ _ => rfl, fun r _ _ _ _ μ 𝓕 _ _ g => ?_⟩
      change ∫ z in 𝓕, (0 : ℂ) ∂μ = 0
      exact integral_zero _ _
    | add x y _ _ hx hy =>
      refine ⟨fun k hk => by rw [map_add, hx.1 k hk, hy.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change x.1 _ + y.1 _ = x.1 g + y.1 g
        rw [hx.2.1, hy.2.1]
      · haveI := hμ
        have ix := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a x (hopen x hx.1)) hx.2.1 μ h𝓕 g
        have iy := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a y (hopen y hy.1)) hy.2.1 μ h𝓕 g
        change ∫ z in 𝓕, (x.1 (unip z * g) + y.1 (unip z * g)) ∂μ = 0
        rw [integral_add ix iy, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, hy.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, add_zero]
    | smul c x _ hx =>
      refine ⟨fun k hk => by rw [map_smul, hx.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change c * x.1 _ = c * x.1 g
        rw [hx.2.1]
      · change ∫ z in 𝓕, c * x.1 (unip z * g) ∂μ = 0
        rw [integral_const_mul, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, mul_zero]
  exact P.2.2

end GlobalTheory.HCFCusp

end
