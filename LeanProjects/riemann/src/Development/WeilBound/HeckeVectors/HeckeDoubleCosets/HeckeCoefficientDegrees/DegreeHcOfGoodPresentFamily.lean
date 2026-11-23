import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDegG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.HeckeCoefficientDegrees.NormDeg

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.D.Upq.Coef

section UJ

open ReciprocityTheory.ChartRestriction.DS

theorem fdeg_gap (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, hc, hH⟩ := fdCons_muG n ε
  refine ⟨c, hc, fun lam h H _ _ _ σ v hl hσ hgap hh hp hq hv => ?_⟩
  have hn : 1 ≤ n := hp.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have ht := thrStar_le hn ε
  refine hH lam H σ v hl hσ h hgap (by linarith) hp hq (fun μ hμ hg => ?_) hv
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
      le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hg hq0 h8
  exact ⟨T, Ψ, hP⟩

theorem fdeg_gap' (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      PI.UpqRep.fdegOf (PI.UpqRep.muG ε) σ v = c * PI.UpqRep.fdegHC lam :=
  fdeg_gap n ε

end UJ

open PI.UpqRep PI.UnitaryGroupMassFormula.FdegHpk in
theorem fdegHpk_gap (k r : ℕ) (hk : 1 ≤ k) (ε : Fin (2 * r + k + 1) → Bool)
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hG : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)) (w : H),
      Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h → w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG σ w = C * fdegHC lam := by
  obtain ⟨cH, hcH, hH⟩ := fdeg_gap' (2 * r + k + 1) ε
  have : SigmaFinite μG := hG.1
  have key : ∀ P, IsCayleyU k r ε P → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      μG = (c • muG ε).map (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P) := by
    intro P hP
    have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0 := by
      rw [hP.1.2]; exact hG.2.2.1
    have hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
      rw [hP.1.2]; intro s hs; exact hG.2.2.2 s hs
    exact PI.UnitaryGroupMassFormula.BesselL2FixAtZero.haar_transport ε P hP.1.1 μG hG.2.1 hconc hinv
  by_cases hex : ∃ P, IsCayleyU k r ε P
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam h H _ _ _ σ w _ hds _ _ _
    obtain ⟨P, hP, -⟩ := hds
    exact absurd ⟨P, hP⟩ hex
  obtain ⟨P₀, hP₀⟩ := hex
  obtain ⟨c₀, hc0, hctop, hμ0⟩ := key P₀ hP₀
  refine ⟨cH / c₀.toReal, div_pos hcH (ENNReal.toReal_pos hc0 hctop), ?_⟩
  intro lam h H _ _ _ σ w hl hds hgap hh hw
  obtain ⟨P, hP, hDS⟩ := hds
  obtain ⟨c, -, hct, hμ⟩ := key P hP
  have hcc : c = c₀ := scale_eq ε hP.1.1 hP₀.1.1 (by rw [hP.1.2, hP₀.1.2]) c c₀ hct (hμ.symm.trans hμ0)
  obtain ⟨hp, hq⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.TransportInt.cayley_signature (k := k) (r := r) (ε := ε) hP.1
  have hp1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by omega
  have hq1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by omega
  have hread := hH lam h H (fun g => σ (P⁻¹ * g * P)) w hl hDS hgap hh hp1 hq1 hw
  have hE := PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_measurableEmbedding ε P hP.1.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hμ, hE.integral_map, integral_smul_measure]
  have hfun : (fun g : UJ ε => ‖⟪w, σ (Matrix.of (PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjPrime₂ ε P g)) w⟫_ℂ‖ ^ 2) =
      fun g => ‖coefOn (ε := ε) (fun g => σ (P⁻¹ * g * P)) w w g‖ ^ 2 := rfl
  rw [hfun, hcc, smul_eq_mul, div_mul_eq_div_div_swap]
  unfold fdegOf at hread
  rw [hread]
  ring

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.Jmu

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq]

theorem degree_hc_of_good_present_family (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq)
    (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) (hF : F.Good p.T.base lam0 q0)
    (hP0 : Present F lam0) : DegHC p F lam0 q0 := by
  have h0 := (hF lam0 (by simp [LatticeNorms.N1]) hP0.1).1
  obtain ⟨C, hC, hd⟩ := fdegHpk_gap P.k P.r h0.2.2.2.1.1 F.ε p.T.base.μG
    h0.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨C, hC, fun μ hμ hp => ?_⟩
  have hG := (hF μ hμ hp.1).1
  obtain ⟨P0, -, hw1, -⟩ := hG.2.2.2.2.1
  have hw0 : (F.A μ).w0 ≠ 0 := fun h => by rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  exact hd _ F.h (F.A μ).H (F.A μ).σ (F.A μ).w0 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1.2.1 hw0

theorem degree_bound_of_hc (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq)
    (lam0 : Fin (2 * P.r + P.k + 1) → ℤ)
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (c0 q0 : ℕ)
    (H : ℝ) (hc0 : P.r + 1 ≤ c0) (hF : F.Good p.T.base lam0 q0) (hP0 : Present F lam0) :
    PieriDegreeConditions p (pieriDataOfFamily p F lam0 tau c0 q0 H) :=
  degree_bound_of_holomorphic_continuation p F lam0 tau c0 q0 H hc0 (normDegree_bound p F lam0 q0 hF)
    CompanionTheory.LimBd.SchurHpk.threeDimData_schurH (degree_hc_of_good_present_family p F lam0 q0 hF hP0) hF hP0

end CompanionTheory.D.Upq.Coef

end
