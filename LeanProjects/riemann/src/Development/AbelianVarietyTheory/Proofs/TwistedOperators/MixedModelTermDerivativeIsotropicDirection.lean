import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem isoPart_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    isoPart V W C (lineAt θ τ z t) = lineAt θ τ (dirAt V W C τ z) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO V W :=
    { toFun := fun t => isoPart V W C (lineAt θ τ z t)
      map_zero' := by unfold isoPart; rw [AddMonoidHom.map_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold isoPart; rw [AddMonoidHom.map_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (dirAt V W C τ z) L := by
    refine ⟨(continuous_isoPart V W C).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (isoPart V W C (lineAt θ τ z t)).map (finPart D) = 0
      unfold isoPart
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (isoPart V W C (lineAt θ τ z t)) = _
      unfold isoPart
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      have e : compAt θ τ' ((adj D C * V.gram).map (incA D)) = (adj D C * V.gram).map (tauE D τ') := by
        unfold compAt
        rw [Matrix.map_map]
        congr 1
        funext e
        exact GlobalTheory.FockCompare.comp_incA hθ τ' e
      rw [e]
      split_ifs with h
      · subst h
        unfold dirAt
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem phase_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hCC : adj D C * V.gram * C' = 1) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    phase ψ V W C C' y (lineAt θ τ z t) = Complex.exp (2 * Real.pi * Complex.I *
      ((t * (2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re) : ℝ) : ℂ)) := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (hL.2.1 t)]
  congr 4
  simp only [hL.2.2 t]
  rw [Finset.sum_eq_single τ (fun b _ hb => by rw [if_neg hb, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    mul_zero]) (by simp), if_pos rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

theorem term_dRho_dirAt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 h G hG τ z y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re := ⟨_, rfl⟩
  rw [← hc]
  have hL'r := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ (dirAt V W C τ z)

  have hg : ∀ t : ℝ, term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y =
      Complex.exp (2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := fun t => by
    rw [← isoPart_lineAt hθ V W C τ z t, GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 h G hG y _,
      phase_lineAt hθ V W C C' hCC hψ y τ z t, hc]
  have hd1 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (2 * Real.pi * Complex.I * (c : ℂ) * term ψ V V' W C C' B μ 𝓨 G y) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) (2 * Real.pi * Complex.I * (c : ℂ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).const_mul (2 * Real.pi * Complex.I)
      simpa using this
    have h2 := (h1.cexp).mul_const (term ψ V V' W C C' B μ 𝓨 G y)
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hg t)

  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : heisO ψ V W (lineAt θ τ (dirAt V W C τ z) 0) (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G := by
    rw [AddMonoidHom.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y) 0 := by
    rw [← e0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓨) (x₀ := (0 : ℝ))
      (F' := fun t x => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D)))
        (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t)
          (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G)) (isoPart V W C x + midPart V V' W B 0))
      (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 t) hG) _ _).aestronglyMeasurable
    · exact integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0) hG) _ _
    · exact (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0)
        (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)) _ _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hK _
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      exact (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL'r hG _ t).const_mul _
  rw [hd2.unique hd1]

end GlobalTheory.MixedTerm.IsoDeriv
