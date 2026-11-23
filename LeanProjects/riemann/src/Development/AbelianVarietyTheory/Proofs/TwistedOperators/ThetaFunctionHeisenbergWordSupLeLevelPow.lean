import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSupBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.LevelSupBound

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm GlobalTheory.SupremumSobolevWords GlobalTheory.HeisTaylor
open scoped NNReal Topology

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem word_theta_level (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (h0 : u.map (infPart D) = 0) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
      heisO ψ S T u f = f → IsThetaFunO ψ S T (wordAct (heisDer ψ θ) l f) ∧
        heisO ψ S T u (wordAct (heisDer ψ θ) l f) = wordAct (heisDer ψ θ) l f := by
  intro l
  induction l with
  | nil => exact fun hf hu => ⟨hf, hu⟩
  | cons a l ih =>
    intro f hf hu
    obtain ⟨h1, h2⟩ := ih hf hu
    have e : wordAct (heisDer ψ θ) (a :: l) f = dv θ σ S T (letter a) (wordAct (heisDer ψ θ) l f) := by
      rw [dv_letter hc hψ]
      rfl
    rw [e]
    exact ⟨theta_dv hc hψ _ h1, dv_level hc hψ _ h0 h2⟩

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (p : ℕ) (f : WO S T → ℂ),
      sobO ψ θ μ 𝓕 p (wordAct (heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (p + l.length) f := by
  intro l
  induction l with
  | nil => intro p f; simp [wordAct]
  | cons a l ih =>
    intro p f
    refine (sobO_heisDer_le p a).trans ?_
    refine (ih (p + 1) f).trans_eq ?_
    congr 1
    simp only [List.length_cons]
    omega

theorem nsmul_fin {u : WO S T} (hinf : u.map (infPart D) = 0) (n : ℕ) : (n • u).map (infPart D) = 0 := by
  ext i j
  have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
  exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))

theorem pointwise (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T))
    (hK₀ : IsCompact K₀) :
    ∃ C : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ y : WO S T,
        ‖f y‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ Module.finrank ℝ (RW T S)) *
          sobO ψ θ μ 𝓕 (Module.finrank ℝ (RW T S)) f := by
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  set N := Module.finrank ℝ (RW T S) with hN
  let b : Module.Basis (Fin N) ℝ (RW T S) := Module.finBasis ℝ (RW T S)
  obtain ⟨c, hcube⟩ := cube_dilate_bound_at hψ hc b h0 hK₀
  let card : ℝ≥0 := Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
  let Q : ℝ≥0 := 1 + card * ‖fun i => b i‖₊
  refine ⟨NNReal.sqrt (4 ^ N * c) * Q ^ N, fun μ 𝓕 hm n hn f hf hl y => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, sobO ψ θ μ 𝓕 N f = s :=
    ⟨_, (ENNReal.coe_toNNReal (sobO_ne_top hψ hθ hm.1 hm.2.1 hf N)).symm⟩
  let ρ : ℝ≥0 := (n : ℝ≥0) * ‖fun i => b i‖₊
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ (ρ : ℝ)) ∧ F = (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • n • b i)) A (c * ((1 + card * ρ) ^ N * s : ℝ≥0) ^ 2) y
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ f ⟨[], le_rfl, by simp, rfl⟩
  · have hQ : 1 + card * ρ ≤ Q * n := by
      have h1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn
      calc 1 + card * ρ ≤ n + card * ρ := add_le_add h1 le_rfl
        _ = Q * n := by simp only [Q, ρ]; ring
    have key' : (‖f y‖₊ : ℝ≥0) ^ 2 ≤ 4 ^ N * (c * ((1 + card * ρ) ^ N * s) ^ 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      simpa using key
    have hb : (‖f y‖₊ : ℝ≥0) ≤ NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s := by
      rw [← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero]
      refine key'.trans ?_
      have e : (NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s) ^ 2 = 4 ^ N * (c * ((Q * n) ^ N * s) ^ 2) := by
        rw [mul_assoc, mul_assoc, mul_pow (NNReal.sqrt _), NNReal.sq_sqrt]
        ring_nf
      rw [e]
      gcongr
    rw [hs, enorm_eq_nnnorm]
    have e2 : ENNReal.ofReal (((NNReal.sqrt (4 ^ N * c) * Q ^ N : ℝ≥0) : ℝ) * (n : ℝ) ^ N) =
        ((NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [e2, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hb
  · rintro p _ ⟨l, h1, h2, rfl⟩
    refine ⟨(wd l).2.cont, fun i => ⟨_, ⟨l ++ [n • b i], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (n • b i) (wd l).2⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        refine norm_nsmul_le.trans ?_
        simp only [ρ, NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => b i) i) (Nat.cast_nonneg n)
    · simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    refine (hcube μ 𝓕 hm n hn _ (wd l).2 (fun u hu hinf => ?_) y).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2) c.coe_nonneg)
    · exact words_level hc hψ (nsmul_fin hinf n) l ⟨f, hf⟩ (hl u hu hinf)
    · refine ENNReal.toReal_le_coe_of_le_coe ((l2O_foldl_dvL_le_pow_mul_sobO hc hψ N l (by simpa using h1) h2 _).trans ?_)
      rw [hs, ← ENNReal.coe_pow, ← ENNReal.coe_mul]

theorem supN_word_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  intro D ψ hψ θ hθ V X K₀ h0 hK₀ μ 𝓕 hm
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨C, hC⟩ := pointwise (S := V) (T := X) hψ hθ h0 hK₀
  refine ⟨Module.finrank ℝ (RW X V), Module.finrank ℝ (RW X V), C, C.2, fun n hn f hf hl l => iSup_le fun y => ?_⟩
  have hw := fun u hu hinf => word_theta_level hc hψ (nsmul_fin (S := V) (T := X) hinf n) l hf (hl u hu hinf)
  have ht : IsThetaFunO ψ V X (wordAct (heisDer ψ θ) l f) :=
    (hw 0 (mem_of_mem_nhds h0) (Matrix.map_zero _ (map_zero _))).1
  refine (hC μ 𝓕 hm n hn _ ht (fun u hu hinf => (hw u hu hinf).2) y).trans ?_
  exact mul_le_mul' le_rfl (sobO_word_le μ 𝓕 l _ f)

end GlobalTheory.LevelSupBound
