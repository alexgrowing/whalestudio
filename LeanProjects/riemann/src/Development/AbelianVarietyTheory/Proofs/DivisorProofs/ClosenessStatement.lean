import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPowerSqrtLeCubeRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerBallIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCompactCoverBoundsStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.CloseReg

theorem asymp : ∀ (A B μ K : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ μ → 0 ≤ K → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 2) + K * t ^ 2 ≤ t ^ ((1 : ℝ) / 3) := GlobalTheory.T.log_power_sqrt_le_cube_root

theorem geom : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P →
    ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ), ∃ (n : ℕ) (ch : Fin n → AlgChart (O.var c).str σ (O.var c).dim)
      (K : Fin n → Set (V (O.var c).dim)) (κ B : ℝ), 0 < κ ∧ 0 ≤ B ∧
      (∀ j, IsCompact (K j) ∧ K j ⊆ (ch j).e.target) ∧ (∀ y, ∃ j, y ∈ (ch j).e.source ∧ (ch j).e y ∈ K j) ∧
      ∀ j, ∀ y ∈ (ch j).e.source, (ch j).e y ∈ K j → y ∈ offBd O.Φ c σ →
        ∀ w ∈ Metric.ball ((ch j).e y) (κ * Real.exp (-(O.met.r c σ y / 2))), w ∈ (ch j).e.target ∧
          (ch j).e.symm w ∈ offBd O.Φ c σ ∧ O.met.r c σ ((ch j).e.symm w) ≤ O.met.r c σ y + B ∧
          ∀ ξ : V (O.var c).dim, P.om c σ (ch j) ((ch j).e.symm w) ξ.ofLp ≤ B * ‖ξ‖ ^ 2 := GlobalTheory.T.chart_compact_cover_bounds

theorem avg : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (a : ChartForm p σ d) (E : ChartMap p σ d) (c : AlgChart p σ d) (f : CxPts p σ → ℝ) (y : CxPts p σ) (t Cc M : ℝ),
    IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → y ∈ c.e.source → 0 < t → 0 < Cc → 0 ≤ M →
    Metric.ball (c.e y) (Cc * t) ⊆ c.e.target →
    (∀ g : CxPts p σ → ℝ, IntegrableOn (g ∘ c.e.symm) (Metric.ball (c.e y) (Cc * t)) →
      Integrable (fun ξ => g (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)) ∧
      |rho a E g y t| ≤ Cc / t ^ (2 * d) * ∫ v in Metric.ball (c.e y) (Cc * t), |g (c.e.symm v)|) →
    (∀ w ∈ Metric.ball (c.e y) (Cc * t), DifferentiableAt ℝ (f ∘ c.e.symm) w ∧ ‖fderiv ℝ (f ∘ c.e.symm) w‖ ≤ M) →
    rho a E f y t - f y ≤ Cc * (volume (Metric.ball (0 : V d) 1)).toReal * Cc ^ (2 * d) * Cc * M * t := GlobalTheory.T.rho_sub_self_le_of_fderiv_le

theorem exists_pos_le {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ t : ℝ, 0 < t ∧ ∀ i, t ≤ f i := by
  haveI := Fintype.ofFinite ι
  have hs : 0 ≤ ∑ i, 1 / f i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hf i)).le
  refine ⟨1 / (1 + ∑ i, 1 / f i), by positivity, fun i => ?_⟩
  have h1 : 1 / f i ≤ ∑ j, 1 / f j :=
    Finset.single_le_sum (f := fun j => 1 / f j) (fun j _ => (one_div_pos.2 (hf j)).le) (Finset.mem_univ i)
  have hfi := hf i
  rw [div_le_iff₀ (by positivity)]
  have : f i * (1 / f i) = 1 := by field_simp
  nlinarith

theorem exp_half_log_mul {t : ℝ} (ht : 0 < t) : Real.exp (Real.log (1 / t) / 2) * t = t ^ ((1 : ℝ) / 2) := by
  calc Real.exp (Real.log (1 / t) / 2) * t = Real.exp (-Real.log t / 2) * Real.exp (Real.log t) := by
        rw [one_div, Real.log_inv, Real.exp_log ht]
    _ = Real.exp (Real.log t * (1 / 2)) := by rw [← Real.exp_add]; ring_nf
    _ = _ := (Real.rpow_def_of_pos ht _).symm

theorem exp_neg_half_log {t : ℝ} (ht : 0 < t) : Real.exp (-(Real.log (1 / t) / 2)) = √t := by
  rw [Real.sqrt_eq_rpow, ← exp_half_log_mul ht, one_div, Real.log_inv]
  rw [show -(-Real.log t / 2) = -Real.log t / 2 + Real.log t by ring, Real.exp_add, Real.exp_log ht]

theorem local_close (hK : KernelSt) {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (h : O.CoreWith x P)
    (Cg μ : ℝ) (hCg : 0 ≤ Cg) (hμ : 0 ≤ μ)
    (hgr : ∀ c σ τ i (ch : AlgChart (O.var c).str σ (O.var c).dim), ∀ y ∈ ch.e.source, y ∈ offBd O.Φ c σ →
      DifferentiableAt ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ∧ ∀ ξ : V (O.var c).dim,
        |fderiv ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ξ| ≤
          Cg * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp))
    (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) :
    ∃ A B t₁ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ τ (i : Fin O.N), ∀ y ∈ offBd O.Φ c σ,
      O.met.r c σ y ≤ Real.log (1 / t) →
      rho (P.om c σ) (P.exph c σ) (psi O x c σ τ i) y t - psi O x c σ τ i y ≤
        A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 2) := by
  obtain ⟨n, ch, Kc, κ, B, hκ, hB, hKc, hcov, hball⟩ := geom D O x P h c σ
  have hka : IsKaehlerForm (AnRead.all (O.var c).str σ (O.var c).dim) (P.om c σ) := P.om_kaehler c σ
  have hE := P.exph_is c σ
  choose Ck tk hCk htk hker using fun j => hK _ _ _ _ _ (P.om c σ) (P.exph c σ) hka hE (ch j) (Kc j) (hKc j).1 (hKc j).2
  have hcore : O.Core := ⟨x, P, h⟩
  obtain ⟨vol, hvol⟩ : ∃ v : ℝ, v = (volume (Metric.ball (0 : V (O.var c).dim) 1)).toReal := ⟨_, rfl⟩
  have hvol0 : 0 ≤ vol := hvol ▸ ENNReal.toReal_nonneg
  obtain ⟨Aj, hAj⟩ : ∃ Aj : Fin n → ℝ, Aj = fun j => Ck j * vol * Ck j ^ (2 * (O.var c).dim) * Ck j := ⟨_, rfl⟩
  have hAj0 : ∀ j, 0 ≤ Aj j := fun j => by have := hCk j; rw [hAj]; positivity
  have hAs : ∀ j, Aj j ≤ ∑ j, Aj j := fun j =>
    Finset.single_le_sum (f := Aj) (fun j _ => hAj0 j) (Finset.mem_univ j)
  have hAs0 : 0 ≤ ∑ j, Aj j := Finset.sum_nonneg fun j _ => hAj0 j
  obtain ⟨t₁, ht₁, ht₁le⟩ := exists_pos_le (fun j => min (tk j) ((κ / Ck j) ^ 2))
    (fun j => lt_min (htk j) (by have := hCk j; positivity))
  refine ⟨(∑ j, Aj j) * Cg * Real.exp (B / 2) * √B, B, t₁, by positivity, hB, ht₁, fun t ht htt τ i y hy hry => ?_⟩
  obtain ⟨j, hyj, hyK⟩ := hcov y
  have htj : t ≤ tk j := htt.trans ((ht₁le j).trans (min_le_left _ _))
  obtain ⟨hbsub, -, hkerj⟩ := hker j y hyj hyK t ht htj
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (1 / t) := ⟨_, rfl⟩
  rw [← hℓ] at hry ⊢
  have hre : Real.exp 1 ≤ O.met.r c σ y := hcore.exp_le_r c σ y
  have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) (hre.trans hry)

  have hrad : Ck j * t ≤ κ * Real.exp (-(O.met.r c σ y / 2)) := by
    have h1 : t ≤ (κ / Ck j) ^ 2 := htt.trans ((ht₁le j).trans (min_le_right _ _))
    have hC := hCk j
    have h2 : √t ≤ κ / Ck j := by
      rw [← Real.sqrt_sq (div_pos hκ hC).le]; exact Real.sqrt_le_sqrt h1
    have h3 : Real.exp (-(ℓ / 2)) = √t := hℓ ▸ exp_neg_half_log ht
    have h4 : Real.exp (-(ℓ / 2)) ≤ Real.exp (-(O.met.r c σ y / 2)) := Real.exp_le_exp.2 (by linarith)
    have h5 : t = √t * √t := (Real.mul_self_sqrt ht.le).symm
    have h6 : Ck j * √t ≤ κ := by rwa [le_div_iff₀ hC, mul_comm] at h2
    have h7 : 0 ≤ √t := Real.sqrt_nonneg t
    calc Ck j * t = (Ck j * √t) * √t := by rw [mul_assoc, ← h5]
      _ ≤ κ * √t := mul_le_mul_of_nonneg_right h6 h7
      _ = κ * Real.exp (-(ℓ / 2)) := by rw [h3]
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hκ.le
  have hpow0 : 0 ≤ (ℓ + B) ^ μ := Real.rpow_nonneg (by linarith) _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Cg * (ℓ + B) ^ μ * Real.exp ((ℓ + B) / 2) * √B := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hder : ∀ w ∈ Metric.ball ((ch j).e y) (Ck j * t), DifferentiableAt ℝ (psi O x c σ τ i ∘ (ch j).e.symm) w ∧
      ‖fderiv ℝ (psi O x c σ τ i ∘ (ch j).e.symm) w‖ ≤ M := by
    intro w hw
    obtain ⟨hwT, hwoff, hwr, hwom⟩ := hball j y hyj hyK hy w (Metric.ball_subset_ball hrad hw)
    have hzs : (ch j).e.symm w ∈ (ch j).e.source := (ch j).e.map_target hwT
    have hzw : (ch j).e ((ch j).e.symm w) = w := (ch j).e.right_inv hwT
    obtain ⟨hd1, hd2⟩ := hgr c σ τ i (ch j) _ hzs hwoff
    rw [hzw] at hd1 hd2
    refine ⟨hd1, ContinuousLinearMap.opNorm_le_bound _ hM0 fun ξ => ?_⟩
    obtain ⟨rz, hrz⟩ : ∃ rz, rz = O.met.r c σ ((ch j).e.symm w) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = P.om c σ (ch j) ((ch j).e.symm w) ξ.ofLp := ⟨_, rfl⟩
    have hd3 := hd2 ξ
    rw [← hrz, ← hq] at hd3
    have hq' := hwom ξ
    rw [← hq] at hq'
    rw [← hrz] at hwr
    have hrz1 : Real.exp 1 ≤ rz := hrz ▸ hcore.exp_le_r c σ _
    have hrz0 : 0 ≤ rz := le_trans (by positivity) hrz1
    have hrz' : rz ≤ ℓ + B := by linarith
    have hp1 : rz ^ μ ≤ (ℓ + B) ^ μ := Real.rpow_le_rpow hrz0 hrz' hμ
    have hp2 : Real.exp (rz / 2) ≤ Real.exp ((ℓ + B) / 2) := Real.exp_le_exp.2 (by linarith)
    have hp3 : √q ≤ √B * ‖ξ‖ := by
      rw [← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_mul hB]
      exact Real.sqrt_le_sqrt hq'
    have hp4 : 0 ≤ rz ^ μ := Real.rpow_nonneg hrz0 _
    rw [Real.norm_eq_abs]
    refine hd3.trans ?_
    have hp5 : Cg * rz ^ μ ≤ Cg * (ℓ + B) ^ μ := mul_le_mul_of_nonneg_left hp1 hCg
    have hp6 : Cg * rz ^ μ * Real.exp (rz / 2) ≤ Cg * (ℓ + B) ^ μ * Real.exp ((ℓ + B) / 2) :=
      mul_le_mul hp5 hp2 (Real.exp_pos _).le (by positivity)
    have hp7 := mul_le_mul hp6 hp3 (Real.sqrt_nonneg _) (by positivity)
    refine hp7.trans_eq ?_
    rw [hM]; ring
  have key := avg _ _ _ _ _ (P.om c σ) (P.exph c σ) (ch j) (psi O x c σ τ i) y t (Ck j) M hka hE hyj ht (hCk j) hM0
    hbsub hkerj hder
  have e1 : Ck j * (volume (Metric.ball (0 : V (O.var c).dim) 1)).toReal * Ck j ^ (2 * (O.var c).dim) * Ck j * M * t =
      Aj j * M * t := by rw [hAj, hvol]
  have e2 : Real.exp ((ℓ + B) / 2) * t = Real.exp (B / 2) * t ^ ((1 : ℝ) / 2) := by
    rw [← exp_half_log_mul ht, ← hℓ, show (ℓ + B) / 2 = ℓ / 2 + B / 2 by ring, Real.exp_add]; ring
  have hMt : 0 ≤ M * t := mul_nonneg hM0 ht.le
  have e3 : (∑ j, Aj j) * M * t = (∑ j, Aj j) * Cg * (ℓ + B) ^ μ * √B * (Real.exp ((ℓ + B) / 2) * t) := by
    rw [hM]; ring
  calc _ ≤ Aj j * M * t := key.trans_eq e1
    _ ≤ (∑ j, Aj j) * M * t := by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (hAs j) hMt
    _ = _ := by rw [e3, e2]; ring

theorem closeSt : Hypotheses2 → HypothesesH → KernelSt → GradSt → CloseSt := by
  intro _ _ hK hG D O x P h hf hR
  obtain ⟨Cg, μ, hCg, hμ, hgr⟩ := hG D O x P h hf hR
  choose A B t₁ hA hB ht₁ hclose using fun c σ => local_close hK O x P h Cg μ hCg hμ hgr c σ
  haveI : Fintype O.s.Comp := Fintype.ofFinite _
  haveI : Fintype (D.what₂.LL →+* ℂ) := Fintype.ofFinite _
  have hle_sum : ∀ (F : O.s.Comp → (D.what₂.LL →+* ℂ) → ℝ), (∀ c σ, 0 ≤ F c σ) → ∀ c σ, F c σ ≤ ∑ c, ∑ σ, F c σ :=
    fun F hF c σ => (Finset.single_le_sum (f := fun σ => F c σ) (fun σ _ => hF c σ) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun c => ∑ σ, F c σ) (fun c _ => Finset.sum_nonneg fun σ _ => hF c σ)
        (Finset.mem_univ c))
  obtain ⟨As, hAs⟩ : ∃ a : ℝ, a = ∑ c, ∑ σ, A c σ := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ b : ℝ, b = ∑ c, ∑ σ, B c σ := ⟨_, rfl⟩
  have hAs0 : 0 ≤ As := hAs ▸ Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun σ _ => hA c σ
  have hBs0 : 0 ≤ Bs := hBs ▸ Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun σ _ => hB c σ
  obtain ⟨t₂, ht₂, hle⟩ := exists_pos_le (fun q : O.s.Comp × (D.what₂.LL →+* ℂ) => t₁ q.1 q.2) fun q => ht₁ _ _
  obtain ⟨t₃, ht₃, hasy⟩ := asymp As Bs μ |P.K| hAs0 hBs0 hμ (abs_nonneg _)
  refine ⟨min t₂ t₃, lt_min ht₂ ht₃, fun t ht htt c σ τ i hi y hy hry => ?_⟩
  have e : P.regFund c σ τ i t y = rho (P.om c σ) (P.exph c σ) (psi O x c σ τ i) y t + P.K * t ^ 2 := if_pos hi
  rw [e]
  have h1 := hclose c σ t ht (htt.trans ((min_le_left _ _).trans (hle (c, σ)))) τ i y hy hry
  have hcore : O.Core := ⟨x, P, h⟩
  have hℓ0 : 0 ≤ Real.log (1 / t) := le_trans (by positivity) ((hcore.exp_le_r c σ y).trans hry)
  have hb : B c σ ≤ Bs := hBs ▸ hle_sum B hB c σ
  have ha : A c σ ≤ As := hAs ▸ hle_sum A hA c σ
  have hp : (Real.log (1 / t) + B c σ) ^ μ ≤ (Real.log (1 / t) + Bs) ^ μ :=
    Real.rpow_le_rpow (by linarith [hB c σ]) (by linarith) hμ
  have hp0 : 0 ≤ (Real.log (1 / t) + B c σ) ^ μ := Real.rpow_nonneg (by linarith [hB c σ]) _
  have hs0 : 0 ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ht.le _
  have h2 : A c σ * (Real.log (1 / t) + B c σ) ^ μ * t ^ ((1 : ℝ) / 2) ≤
      As * (Real.log (1 / t) + Bs) ^ μ * t ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul ha hp hp0 hAs0) hs0
  have h3 : P.K * t ^ 2 ≤ |P.K| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have h4 := hasy t ht (htt.trans (min_le_right _ _))
  linarith

end GlobalTheory.CloseReg
