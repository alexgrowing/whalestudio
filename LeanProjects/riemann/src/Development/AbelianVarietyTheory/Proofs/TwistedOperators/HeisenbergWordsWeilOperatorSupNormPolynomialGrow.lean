import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilWordGrowth

open GlobalTheory.Size

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem wordAct_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    {f f' : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    wordAct (heisDer ψ θ) l (f + f') = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem wordAct_smul (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) (c : ℂ) (f : WO V W → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem wordAct_zero (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) :
    wordAct (heisDer ψ θ) l (0 : WO V W → ℂ) = 0 := by
  have := wordAct_smul (ψ := ψ) (θ := θ) l 0 (0 : WO V W → ℂ)
  rwa [zero_smul, zero_smul] at this

theorem wordAct_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ} (hg : ∀ i, IsThetaFunO ψ V W (g i)) :
    wordAct (heisDer ψ θ) l (∑ i ∈ s, g i) = ∑ i ∈ s, wordAct (heisDer ψ θ) l (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wordAct_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, wordAct_add hψ hθ l (hg i) (theta_finsetSum s fun j _ => hg j), ih]

theorem entry_bound (θ : InfFam D) (A : Matrix (Fin W.rank) (Fin W.rank) ℂ) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (i0 : Fin W.rank) (j0 : Fin V.rank) (c : ℂ) (i : Fin W.rank) (j : Fin V.rank) :
    (A * Matrix.single i0 j0 c * B) i j = A i i0 * c * B j0 j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

end GlobalTheory.WeilWordGrowth

namespace GlobalTheory.WeilWordGrowth

open GlobalTheory.Size

theorem om_pointwise (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (hω : IsWeilDatumO ψ V W χS χT ω) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ N : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, 0 ≤ c ∧ ∀ g h w,
      ‖ω (g, h) f w‖ ≤ c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ N := by
  obtain ⟨N0, hN0⟩ := GlobalTheory.Mem.LiftBound.om_growth D ψ hω.std V W ω (GlobalTheory.Ker.isWeak_of_datum hω) θ hθ
  obtain ⟨N', hN'⟩ := GlobalTheory.Mem.LiftGrow.growth_pair D θ hθ V W N0
  obtain ⟨C1, hC1, hc1⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨C2, hC2, hc2⟩ := GlobalTheory.Grow.height_comparison W hθ
  refine ⟨N', fun f hf => ?_⟩
  have hF : ∀ g h, IsThetaFunO ψ V W (ω (g, h) f) := fun g h => hω.om_pres _ f hf
  let S : GA D V → GA D W → ENNReal := fun g h => ⨆ w, ‖ω (g, h) f w‖ₑ
  have fin : ∀ g h, S g h ≠ ⊤ := fun g h => by
    obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hω.std (hF g h)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC w)
  have hpt : ∀ g h w, ‖ω (g, h) f w‖ ≤ (S g h).toReal := fun g h w => by
    rw [← ENNReal.ofReal_le_iff_le_toReal (fin g h), ofReal_norm_eq_enorm]
    exact le_iSup (fun w => ‖ω (g, h) f w‖ₑ) w
  let K : GA D V → GA D W → ℂ := fun g h => ((S g h).toReal : ℂ)
  have hK : ∀ g h, ‖K g h‖ = (S g h).toReal := fun g h => by
    simp only [K, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hL : ∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h := by
    intro γ hγ δ hδ g h
    have e : S (γ * g) (δ * h) = S g h := by
      have hr := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω γ hγ δ hδ _ (hF g h)
      have e1 : ω (γ * g, δ * h) f = ω (γ, δ) (ω (g, h) f) := by
        rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
      simp only [S, e1]
      refine le_antisymm (iSup_le fun w => ?_) (iSup_le fun w => ?_)
      · rw [← GlobalTheory.AdelicLatMove.actO_actO_inv V W γ δ w, hr]
        exact le_iSup (fun w => ‖ω (g, h) f w‖ₑ) _
      · rw [← hr w]
        exact le_iSup (fun w => ‖ω (γ, δ) (ω (g, h) f) w‖ₑ) _
    simp only [K, e]
  have hR : ∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧
      IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h := by
    obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hω.std V W ω (GlobalTheory.Ker.isWeak_of_datum hω)
      hω.om_cont f hf
    refine ⟨U, U', hU, hU', fun k hk hk2 k' hk' hk2' g h => ?_⟩
    have e1 : ω (g * k, h * k') f = ω (g, h) f := by
      rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, hfix k hk hk2 k' hk' hk2']
    simp only [K, S, e1]
  have hG : ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W,
      ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N0 := by
    intro x y
    obtain ⟨C, hC⟩ := hN0 f hf x y
    refine ⟨C, fun a ha b hb => ?_⟩
    rw [hK]
    have h0 : 0 ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N0 := (norm_nonneg _).trans (hC a ha b hb 0)
    refine ENNReal.toReal_le_of_le_ofReal h0 (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC a ha b hb w)
  obtain ⟨C, hC⟩ := hN' K hL hR hG
  refine ⟨|C| * (C1 * C2) ^ N', by positivity, fun g h w => ?_⟩
  have hh1 := (hc1 g).1
  have hh2 := (hc2 h).1
  have n1 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := NNReal.coe_nonneg _
  have n2 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W h : ℝ) := NNReal.coe_nonneg _
  refine (hpt g h w).trans ((hK g h).symm.le.trans ((hC g h).trans ?_))
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (mul_nonneg n1 n2) ?_ N') (by positivity) (abs_nonneg C)
  calc (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W h : ℝ)
      ≤ (C1 * GlobalTheory.Grow.height V g) * (C2 * GlobalTheory.Grow.height W h) := mul_le_mul hh1 hh2 n2 (n1.trans hh1)
    _ = C1 * C2 * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) := by ring

end GlobalTheory.WeilWordGrowth

namespace GlobalTheory.WeilWordGrowth

open GlobalTheory.Size Formalism.MainNotions.StandardLattice

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

def moveDir (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D V) (h : GA D W) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig W.gram (θ τ) h⁻¹ * z * infMat D.sp.cm.sig V.gram (θ τ) g

theorem heisDer_om {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) {θ : InfFam D} (hθ : IsInfFam θ) (g : GA D V) (h : GA D W)
    (a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    heisDer ψ θ a (ω (g, h) f) = ∑ i, ∑ j,
      ((((moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) i j).re : ℝ) : ℂ) •
          ω (g, h) (heisDer ψ θ (a.1, i, j, false) f) +
        (((moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) i j).im : ℝ) : ℂ) •
          ω (g, h) (heisDer ψ θ (a.1, i, j, true) f)) := by
  have e := GlobalTheory.WeilDeriv.om_dRho_infMat ψ V W χS χT ω hω θ hθ g h a.1
    (moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f hf
  have em : infMat D.sp.cm.sig W.gram (θ a.1) h *
      moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) *
      infMat D.sp.cm.sig V.gram (θ a.1) g⁻¹ = Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) := by
    simp only [moveDir, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (infMat D.sp.cm.sig W.gram (θ a.1) h), ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
      GlobalTheory.PointAtPlaceHom.infMat_one, Matrix.one_mul, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
      GlobalTheory.PointAtPlaceHom.infMat_one, Matrix.mul_one]
  rw [em] at e
  change Formalism.IndefR.Datum.dRho (heisO ψ V W) θ a.1 _ (ω (g, h) f) = _
  rw [← e, dRho_eq_sum_heisDer hω.std hθ hf]
  simp only [map_sum, map_add, map_smul]

theorem norm_moveDir_le (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D V) (h : GA D W) (i0 : Fin W.rank) (j0 : Fin V.rank)
    (b : Bool) (i : Fin W.rank) (j : Fin V.rank) :
    ‖moveDir θ τ g h (Matrix.single i0 j0 (if b then Complex.I else 1)) i j‖ ≤ normInf θ W h * normInf θ V g := by
  rw [moveDir, entry_bound θ, norm_mul, norm_mul]
  have hc : ‖(if b then Complex.I else 1 : ℂ)‖ = 1 := by cases b <;> simp
  rw [hc, mul_one]
  have h1 := GlobalTheory.Mem.LiftBound.entry_le θ W h τ i i0
  have h2 := GlobalTheory.Mem.LiftBound.entry_le θ V g τ j0 j
  exact mul_le_mul (le_of_add_le_of_nonneg_right h1 (norm_nonneg _)) (le_of_add_le_of_nonneg_left h2 (norm_nonneg _))
    (norm_nonneg _) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)

end GlobalTheory.WeilWordGrowth

namespace GlobalTheory.WeilWordGrowth

open GlobalTheory.Size Formalism.MainNotions.StandardLattice GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem words_pointwise (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (hω : IsWeilDatumO ψ V W χS χT ω) (θ : InfFam D)
    (hθ : IsInfFam θ) (k : ℕ) : ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : GA D V) (h : GA D W) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)), l.length ≤ k → ∀ w,
        ‖wordAct (heisDer ψ θ) l (ω (g, h) f) w‖ ≤ c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := by
  induction k with
  | zero =>
    obtain ⟨N, hN⟩ := om_pointwise D ψ V W χS χT ω hω θ hθ
    refine ⟨N, fun f hf => ?_⟩
    obtain ⟨c, hc0, hc⟩ := hN f hf
    refine ⟨c, hc0, fun g h l hl w => ?_⟩
    have e : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    subst e
    exact hc g h w
  | succ k ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨C3, hC3⟩ := GlobalTheory.Grow.normInf_le_height W hθ
    obtain ⟨C4, hC4⟩ := GlobalTheory.Grow.normInf_le_height V hθ
    refine ⟨A + 1, fun f hf => ?_⟩
    have hX : ∀ b : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool, IsThetaFunO ψ V W (heisDer ψ θ b f) :=
      fun b => theta_dRho hθ hω.std b.1 _ hf
    choose cb hcb0 hcb using fun b : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool => hA _ (hX b)
    obtain ⟨c0, hc00, hc0⟩ := hA f hf
    set cs : ℝ := ∑ b, cb b with hcs
    have cs0 : 0 ≤ cs := Finset.sum_nonneg fun b _ => hcb0 b
    set B : ℝ := |C3| * |C4| with hB
    have B0 : 0 ≤ B := by positivity
    refine ⟨c0 + (W.rank * V.rank : ℝ) * (2 * B * cs), by positivity, fun g h l hl w => ?_⟩
    set H : ℝ := GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h with hH
    have H1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (GlobalTheory.Grow.one_le_height V g) (GlobalTheory.Grow.one_le_height W h)
    have H0 : 0 ≤ H := zero_le_one.trans H1
    have HA : 0 ≤ H ^ A := pow_nonneg H0 A
    have hpow : H ^ A ≤ H ^ (A + 1) := pow_le_pow_right₀ H1 (Nat.le_succ A)
    rcases List.eq_nil_or_concat l with e | ⟨L, a, e⟩
    · subst e
      refine (hc0 g h [] (Nat.zero_le _) w).trans ?_
      have : 0 ≤ (W.rank * V.rank : ℝ) * (2 * B * cs) * H ^ (A + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow hc00]
    · rw [List.concat_eq_append] at e
      subst e
      have hL : L.length ≤ k := by simpa using hl
      have hcoef : ∀ (i : Fin W.rank) (j : Fin V.rank),
          ‖moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) i j‖ ≤ B * H := by
        intro i j
        refine (norm_moveDir_le θ a.1 g h a.2.1 a.2.2.1 a.2.2.2 i j).trans ?_
        have n3 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h
        have n4 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) g
        have h3 : normInf θ W h ≤ |C3| * GlobalTheory.Grow.height W h :=
          (hC3 h).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (GlobalTheory.Grow.height_pos W h).le)
        have h4 : normInf θ V g ≤ |C4| * GlobalTheory.Grow.height V g :=
          (hC4 g).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (GlobalTheory.Grow.height_pos V g).le)
        calc normInf θ W h * normInf θ V g ≤ (|C3| * GlobalTheory.Grow.height W h) * (|C4| * GlobalTheory.Grow.height V g) :=
              mul_le_mul h3 h4 n4 (n3.trans h3)
          _ = B * H := by rw [hB, hH]; ring
      have term : ∀ (r : ℝ) (b : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool), |r| ≤ B * H →
          ‖(r : ℂ) * wordAct (heisDer ψ θ) L (ω (g, h) (heisDer ψ θ b f)) w‖ ≤ B * H * (cs * H ^ A) := by
        intro r b hr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul hr ((hcb b g h L hL w).trans (mul_le_mul_of_nonneg_right ?_ HA)) (norm_nonneg _)
          (by positivity)
        exact Finset.single_le_sum (f := cb) (fun b _ => hcb0 b) (Finset.mem_univ b)
      have hT : ∀ (c : ℂ) b, IsThetaFunO ψ V W (c • ω (g, h) (heisDer ψ θ b f)) := fun c b =>
        theta_smul c (hω.om_pres _ _ (hX b))
      have e : wordAct (heisDer ψ θ) (L ++ [a]) (ω (g, h) f) = ∑ i, ∑ j,
          ((((moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) i j).re : ℝ) : ℂ) •
              wordAct (heisDer ψ θ) L (ω (g, h) (heisDer ψ θ (a.1, i, j, false) f)) +
            (((moveDir θ a.1 g h (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) i j).im : ℝ) : ℂ) •
              wordAct (heisDer ψ θ) L (ω (g, h) (heisDer ψ θ (a.1, i, j, true) f))) := by
        rw [wordAct_append]
        change wordAct (heisDer ψ θ) L (heisDer ψ θ a (ω (g, h) f)) = _
        rw [heisDer_om hω hθ g h a hf, wordAct_sum hω.std hθ L _ fun i =>
          theta_finsetSum _ fun j _ => theta_add (hT _ _) (hT _ _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [wordAct_sum hω.std hθ L _ fun j => theta_add (hT _ _) (hT _ _)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [wordAct_add hω.std hθ L (hT _ _) (hT _ _), wordAct_smul, wordAct_smul]
      rw [e]
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans (add_le_add
          (term _ _ ((Complex.abs_re_le_norm _).trans (hcoef i j)))
          (term _ _ ((Complex.abs_im_le_norm _).trans (hcoef i j)))))).trans ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have e2 : B * H * (cs * H ^ A) = B * cs * H ^ (A + 1) := by rw [pow_succ]; ring
      rw [e2]
      have : 0 ≤ c0 * H ^ (A + 1) := by positivity
      nlinarith

end GlobalTheory.WeilWordGrowth

namespace GlobalTheory.WeilWordGrowth

open GlobalTheory.Size

theorem sup_words_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ θ : InfFam D, IsInfFam θ → ∀ d : ℕ, ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d (ω (g, h) f) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D ψ V W χS χT ω hω θ hθ d
  obtain ⟨A, hA⟩ := words_pointwise D ψ V W χS χT ω hω θ hθ d
  refine ⟨A, fun f hf => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hA f hf
  refine ⟨∑ k ∈ Finset.range (d + 1),
    (Fintype.card (Fin k → D.what₂.Tau × Fin W.rank × Fin V.rank × Bool) : ℝ) * c, fun g h => ?_⟩
  set H : ℝ := GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h with hH
  have H0 : 0 ≤ H := mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  have hx : 0 ≤ c * H ^ A := mul_nonneg hc0 (pow_nonneg H0 A)
  have hterm : ∀ k ∈ Finset.range (d + 1), ∀ a : Fin k → D.what₂.Tau × Fin W.rank × Fin V.rank × Bool,
      (⨆ w, ‖wordAct (heisDer ψ θ) (List.ofFn a) (ω (g, h) f) w‖ₑ) ≤ ENNReal.ofReal (c * H ^ A) := by
    intro k hk a
    refine iSup_le fun w => ?_
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal (hc g h _ ?_ w)
    simpa using Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  unfold wordSum
  refine (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hterm k hk a).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.WeilWordGrowth
