import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaLePowOfColProd
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelTheta

def colMajorant {D : D7} (θ : InfFam D) (m : ℕ) (L : Set (Matrix (Fin m) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (N : ℕ) (v : Mx D m 1) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ v i 0‖) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (v.map (finPart D)))

def pureT {D : D7} (θ : InfFam D) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (x : Mx D m n) : ℂ :=
  f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))

theorem pure_le_colMajorant (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧ ∀ N : ℕ, ∃ C : ℝ,
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤
          ENNReal.ofReal C * ∏ j : Fin n, colMajorant θ V.rank L N (fun i (_ : Fin 1) => x i j) := by
  obtain ⟨C0, L, hL, h0⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ 0
  refine ⟨L, hL, fun N => ?_⟩
  obtain ⟨CN, LN, -, hN⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ N
  refine ⟨CN, fun y hy x => ?_⟩
  by_cases hall : ∀ j : Fin n, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L
  · refine (hN y hy x).trans ?_
    gcongr with j _
    unfold colMajorant
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) = 1 :=
      Set.indicator_of_mem (hall j) _
    refine le_trans ?_ (le_of_eq h1.symm)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hz : ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ = 0 := by
      refine le_antisymm ((h0 y hy x).trans (le_of_eq ?_)) bot_le
      rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
      rw [Set.indicator_of_notMem hj, mul_zero, ENNReal.ofReal_zero]
    rw [hz]
    exact bot_le

theorem absTheta_pure_le (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) {c : ℝ} (hc : 0 < c)
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ C₁, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a →
      absTheta V (pureT θ f g) (a * y) ≤
        ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  obtain ⟨L, hL, hmaj⟩ := pure_le_colMajorant D θ hθ V n f g hg C₁ hC₁
  obtain ⟨N₀, hcount⟩ := GlobalTheory.T.theta_rapid_decay_siegel_set D θ hθ V Xf Yf hW hc L hL
  obtain ⟨C', hC'⟩ := hcount N₀ le_rfl
  obtain ⟨C, hC⟩ := hmaj N₀
  refine ⟨max C 0 * max C' 0 ^ n, by positivity, fun y hy t ht a ha => ?_⟩
  have h1 := GlobalTheory.CompanionTheory.ColProd.absTheta_le_pow_of_colProd D V (pureT θ f g) (colMajorant θ V.rank L N₀)
    (ENNReal.ofReal C) y (hC y hy) a
  have hP : 0 ≤ ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have h2 : ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ) ≤
      ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) :=
    (hC' t ht a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP))
  have hpow : (∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n =
      ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring
  calc absTheta V (pureT θ f g) (a * y)
      ≤ ENNReal.ofReal C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ)) ^ n := h1
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max C 0 * max C' 0 ^ n * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg (le_max_right _ _) hP),
          ← ENNReal.ofReal_mul (le_max_right _ _), mul_pow, hpow, mul_assoc]

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Φ : Mx D V.rank n → ℂ), Φ ∈ schwartzA θ V.rank n → ∀ {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (Ω C₀ : Set (GA D V)) (K : Subgroup (GA D V)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D V)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ C : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ k ∈ K, absTheta V Φ (p * a * k) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D V))) := hC₀.mul hK
  obtain ⟨-, m, f, g, hg, hdom⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ hΦ
  have key := fun i => absTheta_pure_le D θ hθ V n (f i) (g i) (hg i) Xf Yf hW hc _ hC₁
  choose Ci hCi0 hCi using key
  refine ⟨∑ i, Ci i, fun p hp t ht a ha k hk => ?_⟩
  have hy : a⁻¹ * p * a * k ∈ C₀ * (K : Set (GA D V)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk
  have hsplit : p * a * k = a * (a⁻¹ * p * a * k) := by group
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  rw [hsplit]
  calc absTheta V Φ (a * (a⁻¹ * p * a * k))
      ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ∑ i, ‖pureT θ (f i) (g i) (invPt V (a * (a⁻¹ * p * a * k)) ξ)‖ₑ :=
        ENNReal.tsum_le_tsum fun ξ => hdom _
    _ = ∑ i, absTheta V (pureT θ (f i) (g i)) (a * (a⁻¹ * p * a * k)) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ i, ENNReal.ofReal (Ci i * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        Finset.sum_le_sum fun i _ => hCi i _ hy t ht a ha
    _ = ENNReal.ofReal ((∑ i, Ci i) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hCi0 i) hP]

end GlobalTheory.CompanionTheory.SiegelTheta
