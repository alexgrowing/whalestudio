import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiablePartialZetaIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableBoundaryZetaTermStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnLowerZetaIntegrandStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerZetaIntegralBoundaryRelationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryZetaTermFunctionalEquationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralFunctionalEquationStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem two_cpow_ne_one {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
  intro h
  have h1 : ‖(2 : ℂ) ^ (-s)‖ = 1 := by rw [← sub_eq_zero.1 h]; simp
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have h3 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

def Jh (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  Bd μ 𝓕 H c s * 2 ^ (-s) / (1 - 2 ^ (-s))

def Ed (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  (1 - 2 ^ (1 - s)) * (Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) - Φ 0 * Jh μ 𝓕 H c s)
    + Φ' 0 * 2 ^ (1 - s) * Bd μ 𝓕 H c (s - 1)

theorem Ed_diff {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ}
    (h1 : Differentiable ℂ (Zp μ 𝓕 H c Φ)) (h2 : Differentiable ℂ (Zp μ 𝓕 H c⁻¹ Φ'))
    (h3 : Differentiable ℂ (Bd μ 𝓕 H c)) : DifferentiableOn ℂ (Ed μ 𝓕 H c Φ Φ') {s | 0 < s.re} := by
  have hp : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ fun s => (2 : ℂ) ^ f s := fun f hf s =>
    (hf s).const_cpow (Or.inl (by norm_num))
  have e1 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (1 - s) := hp _ (by fun_prop)
  have e2 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (-s) := hp _ (by fun_prop)
  have e3 : Differentiable ℂ fun s : ℂ => Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := h2.comp (by fun_prop)
  have e4 : Differentiable ℂ fun s : ℂ => Bd μ 𝓕 H c (s - 1) := h3.comp (by fun_prop)
  have e5 : DifferentiableOn ℂ (Jh μ 𝓕 H c) {s | 0 < s.re} := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((h3 s).mul (e2 s)).div ((differentiableAt_const _).sub (e2 s)) (two_cpow_ne_one hs)
  unfold Ed
  exact (((differentiable_const _).sub e1).differentiableOn.mul
    ((h1.add e3).differentiableOn.sub ((differentiable_const _).differentiableOn.mul e5))).add
    (((differentiable_const _).mul e1).mul e4).differentiableOn

theorem Ed_eq {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : 1 < s.re)
    (hz : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s)
    (h0 : Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = Bd μ 𝓕 H c s * 2 ^ (-s))
    (h1 : Jl μ 𝓕 H c (s - 1) * (1 - 2 ^ (-(s - 1))) = Bd μ 𝓕 H c (s - 1) * 2 ^ (-(s - 1))) :
    Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Zg μ 𝓕 H c Φ s := by
  have n0 := two_cpow_ne_one (s := s) (by linarith)
  have e : Jh μ 𝓕 H c s = Jl μ 𝓕 H c s := by rw [Jh, ← h0, mul_div_assoc, div_self n0, mul_one]
  rw [neg_sub] at h1
  rw [Ed, e, hz]
  linear_combination (-Φ' 0) * h1

theorem Ed_fe {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : Strip s)
    (b0 : Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * Bd μ 𝓕 H c s)
    (b1 : Bd μ 𝓕 H c⁻¹ (-(s - 1)) = 2 ^ (-(s - 1)) * Bd μ 𝓕 H c (s - 1)) :
    (1 - 2 ^ s) * Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Ed μ 𝓕 H c⁻¹ Φ' Φ (1 - s) := by
  have n0 := two_cpow_ne_one (s := s) hs.1
  have n1 := two_cpow_ne_one (s := 1 - s) (by simpa using hs.2)
  have x0 : (2 : ℂ) ^ s ≠ 0 := by simp
  have x1 : (2 : ℂ) ^ (1 - s) ≠ 0 := by simp
  have i0 : (2 : ℂ) ^ (-s) = (2 ^ s)⁻¹ := Complex.cpow_neg _ _
  have i1 : (2 : ℂ) ^ (-(1 - s)) = (2 ^ (1 - s))⁻¹ := Complex.cpow_neg _ _
  rw [neg_sub] at b1
  simp only [Ed, Jh, inv_inv, sub_sub_cancel, show 1 - s - 1 = -s by ring, b0, b1]
  rw [i0] at n0 ⊢
  rw [i1] at n1 ⊢
  generalize (2 : ℂ) ^ s = x at *
  generalize (2 : ℂ) ^ (1 - s) = y at *
  generalize Bd μ 𝓕 H c s = A at *
  generalize Bd μ 𝓕 H c (s - 1) = M at *
  have hx : x - 1 ≠ 0 := fun h => n0 (by rw [sub_eq_zero.1 h]; simp)
  have hy : y - 1 ≠ 0 := fun h => n1 (by rw [sub_eq_zero.1 h]; simp)
  have hx' : 1 - x⁻¹ = (x - 1) / x := by field_simp
  have hy' : 1 - y⁻¹ = (y - 1) / y := by field_simp
  rw [hx', hy']
  field_simp
  ring

end GlobalTheory.CompanionTheory.RSZeta

theorem GlobalTheory.CompanionTheory.RSZeta.functional_equation : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  intro hG1 hG3 hG4a μ 𝓕 mK 𝓓 hS H hH Φ hΦ c hc
  obtain ⟨hΦ', hΦ'', hrel⟩ := hG4a Φ hΦ
  have hci : IsOfFinOrder c⁻¹ := hc.inv
  have hrel' : ∀ g, th (sFA Φ) g + sFA Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ (inv2 g) + Φ 0) := by
    intro g
    have h := hrel (inv2 g)
    rw [GlobalTheory.CompanionTheory.RSZeta.det_inverse_twist_involutive, GlobalTheory.CompanionTheory.RSZeta.module_det_inverse_twist, inv_inv] at h
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (GlobalTheory.CompanionTheory.RSZeta.Dt_pos g).ne']
    simp
  have I1 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c hG1 hS hH hc
  have I2 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci
  have d1 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c hG3 hS hH hΦ
  have d2 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have d1' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c⁻¹⁻¹ hG3 hS hH hΦ
  have d2' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have b1 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c hS hH
  have b2 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c⁻¹ hS hH
  refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c Φ (sFA Φ), GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c⁻¹ (sFA Φ) Φ,
    GlobalTheory.CompanionTheory.RSZeta.Ed_diff d1 d2 b1, GlobalTheory.CompanionTheory.RSZeta.Ed_diff d2' d1' b2, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : 0 < (s - 1).re := by simp; linarith
    have hs0 : 0 < s.re := by linarith
    refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H Φ (sFA Φ) c hG1 hG3 hS hH hΦ hΦ' hrel I1 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s (I1 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc _ (I1 _ hs1)),
      GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H (sFA Φ) Φ c⁻¹ hG1 hG3 hS hH hΦ' hΦ hrel' I2 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci s (I2 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci _ (I2 _ hs1))⟩
  · intro s hs
    exact GlobalTheory.CompanionTheory.RSZeta.Ed_fe hs (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s) (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc (s - 1))
  · intro h1 h0
    apply h1
    have : GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c 0 = 0 := by
      simpa [GlobalTheory.CompanionTheory.RSZeta.Bd] using h0
    simp [GlobalTheory.CompanionTheory.RSZeta.Ed, this]
