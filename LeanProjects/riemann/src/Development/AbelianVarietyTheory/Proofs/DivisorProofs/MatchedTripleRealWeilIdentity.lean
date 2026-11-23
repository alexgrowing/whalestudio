import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairLineDerivativeThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairThetaUniformBoundFamilyStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology Metric

noncomputable section

namespace GlobalTheory.ThetaDeriv

theorem kernel_deriv : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∀ g h, HasDerivAt (fun t : ℝ => theta om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) g h) (theta om' Φ₁ g h) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hd g h
  obtain ⟨m, φ, f, f₁, hφ, hf, hf₁, hlim⟩ := GlobalTheory.T.matched_pair_line_derivative_theta hP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  have := GlobalTheory.T.pair_theta_uniform_bound_family hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.KDecayProof.isPair_small hM.triple) m φ f f₁ hφ hlim g h
  rw [← hf₁] at this
  simpa only [hf] using this

theorem hasDerivAt_thetaIntegral : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∀ h, HasDerivAt (fun t : ℝ => G.M'.I om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) h) (G.M'.I om' Φ₁ h) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd h
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hT := hM.triple
  have hPair := GlobalTheory.KDecayProof.isPair_small hT

  have key : ∀ (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ) k g h', theta om' (om' (1, k) Ψ) g h' = theta om' Ψ g (h' * k) := by
    intro Ψ k g h'
    unfold theta
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  set γt : ℝ → UA σ G.W.J := fun t => γ (Multiplicative.ofAdd t) with hγt
  have hγ0 : γt 0 = 1 := by simp [hγt]
  have hγadd : ∀ s t, γt (s + t) = γt s * γt t := by
    intro s t; simp [hγt, ofAdd_add, map_mul]

  set K : ℝ → UA σ G.V'.J → ℂ := fun t g => theta om' Φ g (h * γt t) with hK
  set K' : ℝ → UA σ G.V'.J → ℂ := fun t g => theta om' Φ₁ g (h * γt t) with hK'
  have hdiff : ∀ g t, HasDerivAt (fun s => K s g) (K' t g) t := by
    intro g t
    have h0 := kernel_deriv hP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hd g (h * γt t)
    have e : (fun u : ℝ => theta om' (om' (1, γ (Multiplicative.ofAdd u)) Φ) g (h * γt t)) = fun u => K (t + u) g := by
      funext u
      rw [key]
      show theta om' Φ g (h * γt t * γt u) = theta om' Φ g (h * γt (t + u))
      rw [hγadd, mul_assoc]
    rw [e] at h0
    have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h0)
    rw [show (fun s => K s g) = fun s => K (t + (s - t)) g from funext fun s => by rw [add_sub_cancel]]
    exact h1

  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hPair
  have hsch : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Ψ ∈ schA F (Fin a' × Fin (a + a')) := fun Ψ hΨ =>
    GlobalTheory.KDecayProof.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΨ).2
  have hcont : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h', Continuous fun g => theta om' Ψ g h' := by
    intro Ψ hΨ h'
    exact ((hB.1 Ψ (hsch Ψ hΨ)).1).comp (continuous_id.prodMk continuous_const)

  have hD := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hPair
  obtain ⟨C, k, hC⟩ := hD Φ (Submodule.mem_inf.1 hΦ).2 0
  obtain ⟨C₁, k₁, hC₁⟩ := hD Φ₁ (Submodule.mem_inf.1 hΦ₁).2 0
  have hγc : Continuous γt := hγ.1.comp (by exact continuous_ofAdd)
  obtain ⟨Cγ, hCγ⟩ : ∃ Cγ : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, (ht (γt t) : ℝ) ≤ Cγ := by
    have hc : Continuous fun t => (ht (γt t) : ℝ) :=
      NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp hγc))
    obtain ⟨Cγ, hCγ⟩ := (isCompact_Icc.image hc).isBounded.bddAbove
    exact ⟨Cγ, fun t ht => hCγ ⟨t, ht, rfl⟩⟩
  have hbd : ∀ (C : ℝ) (k : ℕ) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ g h', ‖theta om' Ψ g h'‖ * (qht g : ℝ) ^ 0 ≤ C * (ht h' : ℝ) ^ k) →
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ g, ‖theta om' Ψ g (h * γt t)‖ ≤ |C| * ((ht h : ℝ) * max Cγ 1) ^ k := by
    intro C k Ψ hCk t htt g
    have e1 := hCk g (h * γt t)
    rw [pow_zero, mul_one] at e1
    refine e1.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) k)).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ k) (abs_nonneg C)
    have h2 : (ht (h * γt t) : ℝ) ≤ (ht h : ℝ) * ht (γt t) := by
      exact_mod_cast heightGL_mul_le F h.1 (γt t).1
    refine h2.trans (mul_le_mul_of_nonneg_left ((hCγ t htt).trans (le_max_left _ _)) (NNReal.coe_nonneg _))
  have hfin : G.M'.μ G.M'.dom ≠ ⊤ :=
    (GlobalTheory.KDecayProof.measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM').ne
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := G.M'.μ.restrict G.M'.dom) (F := K) (F' := K')
    (x₀ := 0) (bound := fun _ => |C₁| * ((ht h : ℝ) * max Cγ 1) ^ k₁) (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun t => (hcont Φ hΦ _).aestronglyMeasurable)
    (Measure.integrableOn_of_bounded (M := |C| * ((ht h : ℝ) * max Cγ 1) ^ k) hfin (hcont Φ hΦ _).aestronglyMeasurable
      (Eventually.of_forall fun g => hbd C k Φ hC 0 ⟨by norm_num, by norm_num⟩ g))
    ((hcont Φ₁ hΦ₁ _).aestronglyMeasurable)
    (Eventually.of_forall fun g t ht' => hbd C₁ k₁ Φ₁ hC₁ t ht' g)
    (Measure.integrableOn_of_bounded (M := ‖|C₁| * ((ht h : ℝ) * max Cγ 1) ^ k₁‖) hfin aestronglyMeasurable_const (Eventually.of_forall fun g => le_rfl))
    (Eventually.of_forall fun g t _ => hdiff g t)
  have e1 : (fun t : ℝ => G.M'.I om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) h) = fun t => ∫ g, K t g ∂(G.M'.μ.restrict G.M'.dom) := by
    funext t
    show ∫ g in G.M'.dom, theta om' (om' (1, γt t) Φ) g h ∂G.M'.μ = ∫ g, K t g ∂(G.M'.μ.restrict G.M'.dom)
    exact integral_congr_ae (Eventually.of_forall fun g => key Φ (γt t) g h)
  have e2 : G.M'.I om' Φ₁ h = ∫ g, K' 0 g ∂(G.M'.μ.restrict G.M'.dom) := by
    show ∫ g in G.M'.dom, theta om' Φ₁ g h ∂G.M'.μ = ∫ g, K' 0 g ∂(G.M'.μ.restrict G.M'.dom)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show theta om' Φ₁ g h = theta om' Φ₁ g (h * γt 0)
    rw [hγ0, mul_one]
  rw [e1, e2]
  exact hmain.2

end GlobalTheory.ThetaDeriv
