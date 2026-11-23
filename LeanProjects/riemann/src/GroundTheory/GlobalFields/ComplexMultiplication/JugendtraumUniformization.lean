import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunctionAutomorphisms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Points

variable {F : Type*} [Field F]

theorem vcPoint_eq_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    (h : C • W = W') (P : W.toAffine.Point) : vcPoint C h P = variableChangePoint C h P := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rfl

theorem pointMapRing_eq_pointMapOfRingHom {L : Type*} [Field L] [DecidableEq F] [DecidableEq L]
    (φ : F →+* L) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    pointMapRing φ W P = pointMapOfRingHom φ P := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rfl

end Points

section Compare

variable {E₁ E₂ : WeierstrassCurve ℂ} [E₁.IsElliptic] [E₂.IsElliptic]

theorem exists_vcPoint_eq_of_isAnalyticUniformization {L : PeriodPair}
    {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    ∃ (D : VariableChange ℂ) (h : D • E₁ = E₂), ∀ z, f₂ z = vcPoint D h (f₁ z) := by
  obtain ⟨C₁, h₁, e₁⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  obtain ⟨C₂, h₂, e₂⟩ := exists_vcPoint_of_isAnalyticUniformization hf₂
  have hinv : C₁⁻¹ • E₁ = weierstrassCurve L := by rw [← h₁, inv_smul_smul]
  refine ⟨C₂ * C₁⁻¹, by rw [mul_smul, hinv, h₂], fun z ↦ ?_⟩
  rw [vcPoint_mul_apply C₂ C₁⁻¹ hinv h₂, e₁ z, e₂ z]
  congr 1
  exact (vcPoint_inv_vcPoint C₁ h₁ _).symm

theorem j_eq_of_smul_eq {D : VariableChange ℂ} (h : D • E₁ = E₂) : E₂.j = E₁.j := by
  rw [← variableChange_j E₁ D]
  exact j_congr h.symm

theorem j_eq_of_isAnalyticUniformization {L : PeriodPair}
    {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    E₂.j = E₁.j := by
  obtain ⟨D, h, -⟩ := exists_vcPoint_eq_of_isAnalyticUniformization hf₁ hf₂
  exact j_eq_of_smul_eq h

theorem weberFunction_eq_of_isAnalyticUniformization {L : PeriodPair} (hE₁ : IsShortForm E₁)
    (hE₂ : IsShortForm E₂) {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂)
    (z : ℂ) : weberFunction E₂ (f₂ z) = weberFunction E₁ (f₁ z) := by
  obtain ⟨D, h, e⟩ := exists_vcPoint_eq_of_isAnalyticUniformization hf₁ hf₂
  rw [e z, vcPoint_eq_variableChangePoint]
  exact weberFunction_variableChangePoint D h hE₁ hE₂ _

end Compare

section Ideal

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

variable {E₁ E₂ : WeierstrassCurve ℂ} [E₁.IsElliptic] [E₂.IsElliptic]

include hK in

theorem exists_unit_automorphismPoint_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ}
    [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    (ξ : MulAction.stabilizer (VariableChange ℂ) E) :
    ∃ ε : (𝓞 K)ˣ, ∀ z, automorphismPoint ξ (f z) =
      f (algebraMap K ℂ (algebraMap (𝓞 K) K ε) * z) := by
  classical
  have hL := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hξ : ξ.1 • E = E := MulAction.mem_stabilizer_iff.mp ξ.2
  have hg := hf.vcPoint ξ.1 hξ
  rw [← hL] at hf hg
  obtain ⟨c, -, hcl, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization hf hg
  rw [hL] at hcl
  obtain ⟨ε, rfl⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl
  refine ⟨ε, fun z ↦ ?_⟩
  have e := hcz z
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply] at e
  rw [automorphismPoint, ← vcPoint_eq_variableChangePoint, e]

end Ideal

end

end Elliptic
end GroundTheory.Global
