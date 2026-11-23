import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {D : D7}

theorem omO_of_single (V W : HSp D) (τ : D.what₂.Tau) (x y : GlobalTheory.FockCompare.RW W V) (hy : ∀ b, b ≠ τ → y b = 0) :
    GlobalTheory.OrientedHeis.omO V W y x = GlobalTheory.OrientedHeis.formAt V W τ (y τ) (x τ) := by
  show ∑ b, GlobalTheory.OrientedHeis.formAt V W b (y b) (x b) = _
  refine Finset.sum_eq_single τ (fun b _ hb => ?_) (by simp)
  rw [hy b hb]
  simp [GlobalTheory.OrientedHeis.formAt]

theorem omO_piW_lineAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    GlobalTheory.OrientedHeis.omO V W (GlobalTheory.FockCompare.piW θ W V ξ) (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1)) =
      -symplAt V W τ z (compAt θ τ ξ) := by
  have skew : ∀ x y, GlobalTheory.OrientedHeis.omO V W x y = -GlobalTheory.OrientedHeis.omO V W y x := fun x y => by
    have e := GlobalTheory.OrientedHeis.omO_self (S := V) (T := W) h (x + y)
    simp only [map_add, LinearMap.add_apply, GlobalTheory.OrientedHeis.omO_self h] at e
    linarith
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt h.inf (m := W.rank) (n := V.rank) τ z
  have hc : ∀ b, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1) b = compAt θ b (lineAt θ τ z 1) := fun b => rfl
  rw [skew, omO_of_single V W τ _ _ (fun b hb => by rw [hc, hL.2.2 1 b, if_neg hb]; rfl), hc, hL.2.2 1 τ, if_pos rfl,
    Complex.ofReal_one, one_smul]
  exact congrArg Neg.neg (GlobalTheory.OrientedRealForm.formAt_eq V W τ z (compAt θ τ ξ))

theorem psi_symplOH_lineAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (t : ℝ) :
    ψ (symplOH V W ξ (lineAt θ τ z t)) =
      Complex.exp ((Real.pi * Complex.I) * ((t * symplAt V W τ z (compAt θ τ ξ) : ℝ) : ℂ)) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines D θ σ h W V).2.1 _
    (GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ z) t
  rw [e, GlobalTheory.OrientedHeis.psi_symplOH h hψ, LinearMap.map_smul, smul_eq_mul, omO_piW_lineAt h]
  congr 1
  push_cast
  ring

theorem dRho_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (ξ : WO V W) {H : WO V W → ℂ}
    (hH : IsThetaFunO ψ V W H) :
    dRho (heisO ψ V W) θ τ z (heisO ψ V W ξ H) =
      heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z H) +
        (-(2 * Real.pi * Complex.I) * (symplAt V W τ z (compAt θ τ ξ) : ℂ)) • heisO ψ V W ξ H := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := ((hA.2.2 θ hθ).1 τ z).1 H hH
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  funext x
  let g : ℝ → ℂ := fun t => heisO ψ V W ξ (heisO ψ V W (lineAt θ τ z t) H) x
  have hfun : (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) =
      fun t : ℝ => Complex.exp (c * (t : ℂ)) * g t := by
    funext t
    simp only [g]
    rw [hU.1 (lineAt θ τ z t) ξ H, hU.1 ξ (lineAt θ τ z t) H, add_comm (lineAt θ τ z t) ξ, skew ξ,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, AddChar.map_neg_eq_inv,
      psi_symplOH_lineAt hψ hθ V W ξ τ z t, ← Complex.exp_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hc]
    push_cast
    ring
  have hg : HasDerivAt g (ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ)) 0 :=
    (hDS (x + ξ)).const_mul _
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * ((0 : ℝ) : ℂ)) * (c * 1)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul c).cexp
  have hg0 : g 0 = heisO ψ V W ξ H x := by
    simp only [g, map_zero]
    unfold heisO
    rw [GlobalTheory.ThetaSquare.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  show deriv (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) 0 = _
  rw [hfun]
  refine (hexp.mul hg).deriv.trans ?_
  rw [hg0]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  show _ = ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ) + _
  ring

theorem pow_bound {X F : Type*} (P : F → Prop) (Dop : F → F) (B : X → F → F → ℂ) (a : X → ℝ)
    (hD : ∀ G, P G → P (Dop G)) (h0 : ∀ G G', P G → P G' → ∃ C : ℝ, ∀ ξ, ‖B ξ G G'‖ ≤ C)
    (h1 : ∀ ξ G G', P G → P G' → |a ξ| * ‖B ξ G G'‖ ≤ ‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :
    ∀ (m : ℕ) (G G' : F), P G → P G' → ∃ C : ℝ, ∀ ξ, |a ξ| ^ m * ‖B ξ G G'‖ ≤ C := by
  intro m
  induction m with
  | zero =>
    intro G G' hG hG'
    obtain ⟨C, hC⟩ := h0 G G' hG hG'
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  | succ m ih =>
    intro G G' hG hG'
    obtain ⟨C₁, hC₁⟩ := ih G (Dop G') hG (hD _ hG')
    obtain ⟨C₂, hC₂⟩ := ih (Dop G) G' (hD _ hG) hG'
    refine ⟨C₁ + C₂, fun ξ => ?_⟩
    calc |a ξ| ^ (m + 1) * ‖B ξ G G'‖ = |a ξ| ^ m * (|a ξ| * ‖B ξ G G'‖) := by ring
      _ ≤ |a ξ| ^ m * (‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :=
        mul_le_mul_of_nonneg_left (h1 ξ G G' hG hG') (by positivity)
      _ = |a ξ| ^ m * ‖B ξ G (Dop G')‖ + |a ξ| ^ m * ‖B ξ (Dop G) G'‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add (hC₁ ξ) (hC₂ ξ)

theorem norm_coef_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (ξ : WO V W) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (hG' : IsThetaFunO ψ V W G') :
    |symplAt V W τ z (compAt θ τ ξ)| * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤
      ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (dRho (heisO ψ V W) θ τ z G' x) ∂ν‖ +
        ‖∫ x in 𝓕, heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) x * star (G' x) ∂ν‖ := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := (hA.2.2 θ hθ).1 τ z
  have hDG := hDS.2.1 G hG
  have e := hDS.2.2 ν 𝓕 hν h𝓕 (heisO ψ V W ξ G) G' (hU.2.2.1 ξ G hG) hG'
  rw [dRho_heisO hψ hθ τ z ξ hG] at e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  have hI1 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hDG) hG'
  have hI2 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hG) hG'
  have hsplit : GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) + c • heisO ψ V W ξ G) G' =
      GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' + c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' := by
    unfold GlobalTheory.Ker.ipO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add hI1 (hI2.const_mul c), integral_const_mul]
  rw [hsplit] at e
  have e2 : c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' =
      -GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G') -
        GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' := by
    linear_combination e
  have hn : ‖c‖ = 2 * Real.pi * |a| := by
    rw [hc, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have h3 : ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤
      ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G')‖ +
        ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G'‖ := by
    rw [← norm_mul, e2, sub_eq_add_neg, ← neg_add]
    rw [norm_neg]
    exact norm_add_le _ _
  have h4 : |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤ ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by
    rw [hn]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h0 : 0 ≤ |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by positivity
    nlinarith
  exact h4.trans h3

theorem norm_coef_bdd {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G)
    (hG' : IsThetaFunO ψ V W G') :
    ∃ C : ℝ, ∀ ξ : WO V W, ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  have hSI := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1
  obtain ⟨a, ha⟩ := (hSI G hG).2.1
  obtain ⟨b, hb⟩ := (hSI G' hG').2.1
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hν h𝓕).2
  refine ⟨a * b * (ν 𝓕).toReal, fun ξ => ?_⟩
  refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0))

theorem coef_decay : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ ξ : WO V W, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ ξ)| ^ m * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
  have hDS := (((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).2.2 θ hθ).1 τ z
  exact pow_bound (IsThetaFunO ψ V W) (dRho (heisO ψ V W) θ τ z)
    (fun ξ F F' => ∫ x in 𝓕, heisO ψ V W ξ F x * star (F' x) ∂ν) (fun ξ => symplAt V W τ z (compAt θ τ ξ))
    (fun F hF => hDS.2.1 F hF) (fun F F' hF hF' => norm_coef_bdd hψ hν h𝓕 hF hF')
    (fun ξ F F' hF hF' => norm_coef_le hψ hθ hν h𝓕 τ z ξ hF hF') m G G' hG hG'

end GlobalTheory.ThetaDecay

end
