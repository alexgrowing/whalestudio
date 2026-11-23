import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainLoweringStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaisingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntCoordsOfRegularParam
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointApplyOfNormPreserving
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqAdjointAddGeOfJointEigenspaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChainLowerBound
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem exists_shifted_types_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ k r z π u l n₀ b hz hT hπ hreg hl1 hlk hgap hb hn hb1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < n := by omega
  let i : Fin n := ⟨m, hm⟩
  obtain ⟨β, L, hL, hu, hd⟩ := GlobalTheory.exists_int_coords_of_regular_param n u (by simpa using hreg)
  obtain ⟨B, hB⟩ := (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).1
  have hgapZ : L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc := by
    have h := hd i.castSucc i.succ
    simp only [Fin.val_succ, Fin.val_castSucc, i] at h
    have : ((L i.succ + 2 * (n₀ : ℤ) + 1 : ℤ) : ℝ) ≤ ((L i.castSucc : ℤ) : ℝ) := by
      push_cast
      simp only [i]
      linarith
    exact_mod_cast this
  have hwide : (L 0 : ℝ) - (L (Fin.last n) : ℝ) ≤ 2 * b := by
    rw [hd]
    have h1 := abs_le.mp (hb (((0 : Fin (n + 1)) : ℕ) + 1) (by simp))
    have h2 := abs_le.mp (hb (((Fin.last n : Fin (n + 1)) : ℕ) + 1) (by simp))
    linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, πp, Ap, hπp, hAp, hwp⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_raising V n r z π u β L B i.succ n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hj
      have := hL.antitone hj'
      omega)
  obtain ⟨Vm, familyMassRatio, familyMassSecondLine, iM3, πm, Am, hπm, hAm, hwm⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_lowering V n r z π u β L B i.castSucc n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
      have := hL.antitone hj'
      omega)
  refine ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, ?_⟩
  refine GlobalTheory.WigSh.lower_bound_spreads V Vp Vm n r z π πp πm B Ap Am n₀ b hz hT hπ.2.2.2.1 hπp.2.2.2.1
    hπm.2.2.2.1 hB hAp hAm ?_
  intro v
  have hyp := (GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB).1
  have hdec := (Formalism.FourierDecayAlt.P.branching_decomposition V n (EB π B) β L hyp).2
  have hspan : ⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA (EB π B)) (shf β M.1) = ⊤ := by
    rw [← hdec, iSup_subtype]
  have key := GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces V Vp Vm {M : Fin n → ℤ // Box L M}
    (fun M => CapSp (subA (EB π B)) (shf β M.1)) (Ap (B (Fin.last n))) (Am (B (Fin.last n))) _ _
    ((3 * b) ^ (2 * n₀))⁻¹ hspan (fun M w hw => ⟨hwp M.1 w hw, hwm M.1 w hw⟩)
    (fun M => GlobalTheory.WigSh.chain_lower_bound n L M.1 i n₀ b hL M.2 hgapZ hb1 hn hwide) v
  have hpos : 0 < (3 * b) ^ (2 * n₀) := by positivity
  rwa [inv_mul_le_iff₀ hpos] at key

end GlobalTheory.WigSh
