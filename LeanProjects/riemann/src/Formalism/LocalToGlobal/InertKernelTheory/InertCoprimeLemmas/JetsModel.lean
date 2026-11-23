import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.TestVectorMemSchwartzBruhat
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneDatumExistence
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls

noncomputable section

namespace Formalism.L2.KerInert

namespace JetsModel

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem eisenstein_invariants_algebraic (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    g2 (lamOf D cc δ) ∈ Qbar ∧ g3 (lamOf D cc δ) ∈ Qbar := by
  have hδ0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc.1 hδ0
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcc hδ L hL
  obtain ⟨e2, e3⟩ :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL)
  rw [e2, e3]
  exact ⟨hg2, hg3⟩

theorem wModel_Δ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : (wModel lam (lamOf D cc δ)).Δ = 1 := by
  obtain ⟨h2, h3⟩ := eisenstein_invariants_algebraic D cc δ hcc hδ
  set a2 : Qbar := ⟨g2 (lamOf D cc δ), h2⟩ with ha2
  set a3 : Qbar := ⟨g3 (lamOf D cc δ), h3⟩ with ha3
  have ea4 : lamC lam (-(g2 (lamOf D cc δ)) / 4) = lam (-a2 / 4) := by
    have : -(g2 (lamOf D cc δ)) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe]
  have ea6 : lamC lam (-(g3 (lamOf D cc δ)) / 4) = lam (-a3 / 4) := by
    have : -(g3 (lamOf D cc δ)) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe]
  have hd : a2 ^ 3 - 27 * a3 ^ 2 = 1 := by
    apply Subtype.ext
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    push_cast
    exact this
  have hw : wModel lam (lamOf D cc δ) = ⟨0, 0, 0, lam (-a2 / 4), lam (-a3 / 4)⟩ := by
    simp only [wModel, ea4, ea6]
  have key : lam (a2 ^ 3 - 27 * a3 ^ 2) = 1 := by rw [hd, map_one]
  rw [hw, ← key]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat]
  ring

theorem epsilon_unit : VariableChangeUnitIntegralAtInertPrimes := by
  intro D cc δ hcc hδ p _ h5 hIn lam C hC
  obtain ⟨-, -, -, -, -, hΔ⟩ := hC
  have e : (C • wModel lam (lamOf D cc δ)).Δ = 1 := hΔ
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ D cc δ hcc hδ lam, mul_one] at e
  have hn : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    have := congrArg norm e
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  unfold IsIntP
  rw [show ((C.u : ℂ_[p]ˣ) : ℂ_[p]) = (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))⁻¹ by simp, norm_inv, hn, inv_one]

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem integral_model_exists : ModelExists := by
  intro D cc δ hcc hδ p _ h5 hIn lam
  obtain ⟨cc', δ', g, -, -, hlat, hgl, hAt, -, -⟩ :=
    Formalism.L2.KerInert.GenusOneDatumExistence.genus_one_datum_exists_lattice Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcc hδ p h5 hIn lam
  obtain ⟨-, -, -, hgL, hU, -⟩ := hAt
  have hU' : Formalism.MainNotions.GL3Theta.IsModelU lam (lamOf D cc δ) g.C := by
    rw [← hgl, ← hlat, ← hgL]; exact hU
  obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hU'
  set W' := g.C • wModel lam (lamOf D cc δ) with hW'
  have hΔ' : ‖W'.Δ‖ = 1 := hΔ
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq W'.Δ (show 0 < 12 by norm_num)
  have hν1 : ‖ν‖ = 1 := by
    have := congrArg norm hν
    rw [norm_pow, hΔ'] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν1; exact zero_ne_one hν1
  let S : WeierstrassCurve.VariableChange ℂ_[p] := ⟨Units.mk0 ν hν0, 0, 0, 0⟩
  refine ⟨S * g.C, Formalism.L2.Th1.A.wU ((S * g.C) • wModel lam (lamOf D cc δ)), ?_,
    Formalism.L2.KerInert.GenusOneDatumExistence.isWq_wU _⟩
  have hSW : (S * g.C) • wModel lam (lamOf D cc δ) = S • W' := mul_smul _ _ _
  have hSu : ((S.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ := by simp [S]
  have hn : ‖ν⁻¹‖ = 1 := by rw [norm_inv, hν1, inv_one]
  show IsIntP ((S * g.C) • wModel lam (lamOf D cc δ)).a₁ ∧ IsIntP ((S * g.C) • wModel lam (lamOf D cc δ)).a₂ ∧
    IsIntP ((S * g.C) • wModel lam (lamOf D cc δ)).a₃ ∧ IsIntP ((S * g.C) • wModel lam (lamOf D cc δ)).a₄ ∧
    IsIntP ((S * g.C) • wModel lam (lamOf D cc δ)).a₆ ∧ ((S * g.C) • wModel lam (lamOf D cc δ)).Δ = 1
  rw [hSW]
  unfold IsIntP at h1 h2 h3 h4 h6 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.variableChange_a₁, hSu]
    simp only [S, mul_zero, add_zero, norm_mul, hn, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hSu]
    simp only [S, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hn, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hSu]
    simp only [S, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hSu]
    simp only [S, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hn,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hSu]
    simp only [S, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hn, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hSu, ← hν, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν0)]

end JetsModel

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem jetsInert_of_int : IntInert → OrthBasisExists → PhiJetInt → JetsInert :=
  fun hInt hOB hPJ => jetsInert_of hInt hOB JetsModel.integral_model_exists JetIntegrality.log_derivative_integral
    JetsModel.epsilon_unit hPJ

end Formalism.L2.KerInert
