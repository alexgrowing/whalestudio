import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCostStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev supWord (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (k : ℕ) (G : WO V W → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G

theorem enorm_real_cast {a : ℝ} (h : 0 ≤ a) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg h]

def opAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  G - (((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) • derAlong ψ θ V W C x (derAlong ψ θ V W C x G)

theorem theta_derAlong {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : IsThetaFunO ψ V W (derAlong ψ θ V W C x G) := by
  obtain ⟨U, -, hU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hG
  unfold derAlong
  exact GlobalTheory.Size.theta_finsetSum Finset.univ fun τ _ => (GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hU τ _).1

theorem theta_sub_smul {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {G H : WO V W → ℂ} (c : ℂ)
    (hG : IsThetaFunO ψ V W G) (hH : IsThetaFunO ψ V W H) : IsThetaFunO ψ V W (G - c • H) := by
  have h := GlobalTheory.OrientedHeis.theta_add hG (GlobalTheory.OrientedHeis.theta_smul (-c) hH)
  rwa [neg_smul, ← sub_eq_add_neg] at h

theorem term_opAlong {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (x y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C x G) y =
      ((1 + ratPair W y x ^ 2 : ℝ) : ℂ) * term ψ V V' W C C' B μ 𝓨 G y := by
  have hG1 := theta_derAlong hψ hθ C x hG
  have hG2 := theta_derAlong hψ hθ C x hG1
  obtain ⟨hadd, hsmul⟩ := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hμ y
  have e1 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ G hG x y
  have e2 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ _ hG1 x y
  have hsplit : opAlong ψ θ V W C x G = G + (-(((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) •
      derAlong ψ θ V W C x (derAlong ψ θ V W C x G) := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  rw [hsplit, hadd _ _ hG (GlobalTheory.OrientedHeis.theta_smul _ hG2), hsmul _ _ hG2, e2, e1]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (4 * (Real.pi : ℂ) ^ 2)⁻¹ * (4 * (Real.pi : ℂ) ^ 2) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ))
  push_cast
  linear_combination (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y * Complex.I ^ 2) * hc +
    (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y) * Complex.I_sq

theorem term_decay {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    (l : List (Matrix (Fin W.rank) (Fin r) D.host.E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ y,
      ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod ≤
        ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) G := by
  induction l with
  | nil =>
    refine ⟨1, zero_le_one, fun G _ y => ?_⟩
    simp only [List.map_nil, List.prod_nil, mul_one, ENNReal.ofReal_one, one_mul, List.length_nil,
      mul_zero]
    unfold supWord
    rw [GlobalTheory.Size.wordSum_zero]
    exact GlobalTheory.T.enorm_mixedModelTerm_le_iSup D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  | cons a l ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨hsub, hder⟩ := GlobalTheory.T.supNormWordSum_sub_le_and_derivative_cost D V W ψ hψ θ hθ
    obtain ⟨c₀, hc₀, hd⟩ := hder r C a
    have he0 : (0 : ℝ) ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
    refine ⟨K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀), by positivity, fun G hG y => ?_⟩
    have hG1 := theta_derAlong hψ hθ C a hG
    have hG2 := theta_derAlong hψ hθ C a hG1
    have hop : IsThetaFunO ψ V W (opAlong ψ θ V W C a G) :=
      theta_sub_smul ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) hG hG2
    have hp : (0 : ℝ) ≤ 1 + ratPair W y a ^ 2 := by positivity
    have hterm : ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ =
        ENNReal.ofReal (1 + ratPair W y a ^ 2) * ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ := by
      rw [term_opAlong hs h1 hψ hθ hμ hG a y, enorm_mul, enorm_real_cast hp]
    have hlen : 2 * (a :: l).length = 2 * l.length + 1 + 1 := by
      simp only [List.length_cons]
      ring
    have hsize : supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) ≤
        ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * (a :: l).length) G := by
      rw [hlen]
      have s1 := hsub G _ ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) (2 * l.length) hG hG2
      have s2 := hd _ hG1 (2 * l.length)
      have s3 := hd G hG (2 * l.length + 1)
      have s4 := GlobalTheory.Size.wordSum_mono (A := GlobalTheory.Size.heisDer ψ θ)
        (p := fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (show 2 * l.length ≤ 2 * l.length + 1 + 1 by omega) G
      rw [enorm_real_cast he0] at s1
      calc supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G)
          ≤ supWord ψ θ V W (2 * l.length) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              supWord ψ θ V W (2 * l.length) (derAlong ψ θ V W C a (derAlong ψ θ V W C a G)) := s1
        _ ≤ supWord ψ θ V W (2 * l.length + 1 + 1) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              (ENNReal.ofReal c₀ * (ENNReal.ofReal c₀ * supWord ψ θ V W (2 * l.length + 1 + 1) G)) := by
            gcongr
            exact s2.trans (by gcongr)
        _ = ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * l.length + 1 + 1) G := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul he0]
            ring
    rw [List.map_cons, List.prod_cons]
    calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (ENNReal.ofReal (1 + ratPair W y a ^ 2) *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod)
        = ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod := by
          rw [hterm]
          ring
      _ ≤ ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) := hb _ hop y
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) *
          supWord ψ θ V W (2 * (a :: l).length) G) := by gcongr
      _ = ENNReal.ofReal (K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀)) *
          supWord ψ θ V W (2 * (a :: l).length) G := by
          rw [ENNReal.ofReal_mul hK]
          ring

theorem mixed_terms_bound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  intro D V V' W r C C' B hs h1 _ _ ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨e, he⟩ := GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨n, X, hXint, hXsep⟩ := GlobalTheory.T.exists_integral_matrices_separating_rationalPairing D W r
  obtain ⟨K₀, hK₀, hdec⟩ := term_decay hs h1 hψ hθ hμ (List.ofFn X)
  refine ⟨2 * e * n, 2 * n, fun U hU => ?_⟩
  obtain ⟨M, _, hN⟩ := he U hU
  refine ⟨K₀ * (5 * (M : ℝ) ^ 2) ^ n, fun g h F hF hfix => ?_⟩
  obtain ⟨N, hNpos, hNle, hint⟩ := hN g h
  have hg1 := (GlobalTheory.Size.height_laws V).1 g
  have hh1 := (GlobalTheory.Size.height_laws W).1 h
  have ht0 : (0 : ℝ) ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (by linarith) (by linarith)
  have hbound := GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay (Y := Matrix (Fin W.rank) (Fin r) D.host.E) n N hNpos
    (fun y => ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ) (fun j y => ratPair W y (X j))
    (fun y y' _ _ hyy => hXsep y y' hyy)
    (fun y hy j => hint F hF hfix y (enorm_ne_zero.mp hy) (X j) (hXint j))
    (ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F)
    (fun y => by
      have hy := hdec F hF y
      rw [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hy
      exact hy)
  have hNM : (5 * (N : ℝ) ^ 2) ^ n ≤
      (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by
    calc (5 * (N : ℝ) ^ 2) ^ n
        ≤ (5 * ((M : ℝ) * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e) ^ 2) ^ n := by gcongr
      _ = (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by ring
  show ∑' y, ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ ≤ _
  refine hbound.trans ?_
  calc ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n)
      ≤ ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (M : ℝ) ^ 2) ^ n *
          (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) := by gcongr
    _ = ENNReal.ofReal (K₀ * (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) *
          supWord ψ θ V W (2 * n) F := by
        rw [mul_assoc K₀, ENNReal.ofReal_mul hK₀]
        ring

end GlobalTheory.MixedTerm

end
