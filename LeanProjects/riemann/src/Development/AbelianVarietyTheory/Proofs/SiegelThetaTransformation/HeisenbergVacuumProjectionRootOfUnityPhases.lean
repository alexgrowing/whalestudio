import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndexStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMuStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualVacuumGaussianShapeRootOfUnityPhasesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenbergStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Proj

section General

variable {α β : Type} [Fintype α] [Fintype β]

theorem ip_smul_smul {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hlin := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.1 (a * conj b)
  have hfun : (fun x => (a • φ) x * conj ((b • ψ) x)) = (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  show haar (fun x => (a • φ) x * conj ((b • ψ) x)) = a * conj b * haar (φ * fun x => conj (ψ x))
  rw [hfun, hlin]

theorem ip_conj {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ip ψ φ = conj (ip φ ψ) := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hc := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.2.1
  have hfun : (fun x => ψ x * conj (φ x)) = fun x => conj ((φ * fun x => conj (ψ x)) x) := by
    funext x
    simp only [Pi.mul_apply, map_mul, Complex.conj_conj]
    ring
  show haar (fun x => ψ x * conj (φ x)) = conj (haar (φ * fun x => conj (ψ x)))
  rw [hfun, hc]

theorem ph_ip [DecidableEq β] {φ ψ : Matrix α β ℚ → ℂ} (hφ : PV φ) (hψ : PV ψ) : Ph (ip φ ψ) := by
  have sφ : Shape φ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β φ).2.1 hφ
  have sψ : Shape ψ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β ψ).2.1 hψ
  have sψc : Shape (fun x => conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β ψ sψ).1
  have spr : Shape (fun x => φ x * conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β φ sφ).2.2 _ sψc
  exact GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase α β _ spr

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isVac_smul {w : E} {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {v : TF n g}
    (hv : IsVac X bas w A v) {u : ℂ} (hu : ‖u‖ = 1) : IsVac X bas w A (u • v) := by
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨hsb, hip, hfix⟩ := hv'
  unfold IsVac
  refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hsb hsb).2.1 u, ?_, ?_⟩
  · rw [ip_smul_smul hsb hsb, hip, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  · intro y hy
    have hlin : heisG X bas y (u • v) = u • heisG X bas y v := by
      funext x
      simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, smul_comm, hfix y hy]

theorem unitv_smul {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) (c : ℂ) :
    unitv (c • v) = (((‖c‖ : ℝ) : ℂ)⁻¹ * c) • v := by
  have hc : ip (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip_smul_smul hv hv, h1, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold unitv
  rw [hc, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg c), smul_smul]

theorem proj_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL v hv
  have hstd : stdL E n ∈ Vset E n 1 := GlobalTheory.SW.Base.stdL_mem_Vset n 1
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨A, ε, hA⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL (stdL E n) hstd v hv
  obtain ⟨u, hu1, hupv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) v).2.2.1 A ε hA
  refine ⟨u, hu1, fun Λ hΛ => ?_⟩
  have H := GlobalTheory.T.tensorLattice_vacua_exist_unique E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ
  obtain ⟨vΛ, hvΛ⟩ := H.1
  have hvΛ' := hvΛ
  unfold IsVac at hvΛ'
  have hproj : projA X bas w (tens Λ L) v = ip v vΛ • vΛ := H.2.2.1 v hv'.1 vΛ hvΛ
  have hnorm := H.2.2.2 L hL (stdL E n) hstd vΛ v hvΛ hv
  rw [(GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ).2.2.2.2.2 (stdL E n) hstd,
    ip_conj hv'.1 hvΛ'.1, Complex.norm_conj] at hnorm
  have hsq := congrArg Real.sqrt hnorm
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at hsq
  have hc0 : ‖ip v vΛ‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsq
    exact zero_ne_one hsq
  have hunit : unitv (projA X bas w (tens Λ L) v) = (((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ) • vΛ := by
    rw [hproj]
    exact unitv_smul hvΛ'.1 hvΛ'.2.1 _
  have he : ‖((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hunit]
    exact isVac_smul hvΛ he
  · obtain ⟨A', ε', hA'⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL Λ hΛ vΛ hvΛ
    obtain ⟨u', hu'1, hu'pv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) vΛ).2.2.1 A' ε' hA'
    have hph : Ph (ip (u • v) (u' • vΛ)) := ph_ip hupv hu'pv
    have hu'u : conj u' * u' = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu'1]
      simp
    have heq : u • unitv (projA X bas w (tens Λ L) v) =
        (ip (u • v) (u' • vΛ) * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹) • (u' • vΛ) := by
      rw [hunit, ip_smul_smul hv'.1 hvΛ'.1, smul_smul, smul_smul]
      congr 1
      linear_combination (-(u * ip v vΛ * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹)) * hu'u
    rw [heq]
    exact (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) (u' • vΛ)).2.2.2.1 hu'pv _
      (Ph.mul hph (Ph.inv ((GlobalTheory.T.complex_phase_calculus_rootOfUnity).2.2.1 ‖ip v vΛ‖)))
  · have hC : ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ) *
        ((‖ip v vΛ‖ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
    rw [hunit, hproj, smul_smul, ← _root_.mul_assoc, ← _root_.mul_inv, hC, inv_one, _root_.one_mul]

end GlobalTheory.Phase.Proj
