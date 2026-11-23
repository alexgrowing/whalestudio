import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMatchedDescentIdentity

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKLieTriple

open scoped Classical in

theorem hasDerivAt_theta_line (hP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.V'.J) (hγ : γ ∈ Lines σ G.V')
    (Φ : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    (Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0)
    (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    HasDerivAt (fun t : ℝ => theta om' Φ (g * γ (Multiplicative.ofAdd t)) h) (theta om' Φ₁ g h) 0 := by
  have hsch := GlobalTheory.KDecayProof.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ).2
  obtain ⟨n, c, s, hs⟩ := Submodule.mem_span_set'.1 hsch
  choose f0 φ hφ hfe using fun i => (s i).2
  choose u u₁ hu hu₁ using fun i : Fin n => GlobalTheory.T.weil_line_good_model_polynomial hP.base G.M' B.ψ _ _ om' hT.base.std hT.geo.hM' hT.weil' γ hγ
    (c i • f0 i) _ (GlobalTheory.ThetaDerivFirst.rest_fin (c i • f0 i) (hφ i))
  have hΦe : Φ = ∑ i, pureA F (c i • f0 i) (φ i) := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfe i]
    funext x
    simp [pureA, mul_assoc]
  have horb : ∀ t : ℝ, om' (γ (Multiplicative.ofAdd t), 1) Φ = ∑ i, pureA F (u i t) (φ i) := by
    intro t
    rw [hΦe, map_sum]
    exact Finset.sum_congr rfl fun i _ => hu i t
  have hΦ₁ : Φ₁ = ∑ i, pureA F (u₁ i) (φ i) := by
    funext x
    set y : Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F :=
      fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
    set z : Fin a' × Fin (a + a') → Af F := fun j => (x j).2
    have hder : ∀ i, HasDerivAt (fun t : ℝ => u i t y) (u₁ i y) 0 := by
      intro i
      rw [hasDerivAt_iff_tendsto_slope]
      let ev : SInf F (Fin a' × Fin (a + a')) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)
      have h1 := (ev.continuous.tendsto (u₁ i)).comp (hu₁ i)
      have e2 : ev (u₁ i) = u₁ i y := rfl
      rw [e2] at h1
      refine h1.congr' (Eventually.of_forall fun t => ?_)
      simp [ev, slope_def_module]
    have hsum : HasDerivAt (fun t : ℝ => ∑ i, u i t y * φ i z) (∑ i, u₁ i y * φ i z) 0 :=
      HasDerivAt.fun_sum fun i _ => (hder i).mul_const _
    have e1 : (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) = fun t => ∑ i, u i t y * φ i z := by
      funext t
      rw [horb, Finset.sum_apply]
      rfl
    have h3 := hd x
    rw [e1] at h3
    rw [h3.unique hsum, Finset.sum_apply]
    rfl
  have key : ∀ k, theta om' Φ (g * k) h = theta om' (om' (k, 1) Φ) g h := by
    intro k
    unfold theta
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have h4 := GlobalTheory.T.pair_theta_uniform_bound_family hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.KDecayProof.isPair_small hT) n φ (fun t i => u i t) u₁
    hφ hu₁ g h
  rw [← hΦ₁] at h4
  simpa only [key, horb] using h4

theorem lie_kills : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ γ ∈ Lines σ G.V', ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      (∀ x, HasDerivAt (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → G.M'.I om' Φ₁ = 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hP hT γ hγ Φ hΦ Φ₁ hΦ₁ hd
  have hPair := GlobalTheory.ThKContSmall.isPair_small hT
  have hSo : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Ψ ∈ G.M'.So B.ψ B.τ₁ := fun Ψ hΨ => (Submodule.mem_inf.1 hΨ).2
  have hS : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Ψ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun Ψ hΨ => GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ (hSo Ψ hΨ)
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hv⟩
  have hL1 := hasDerivAt_theta_line hP hT γ hγ Φ hΦ Φ₁ hd
  funext h
  have hconst : ∀ s : ℝ, ∫ g in G.M'.dom, theta om' Φ (g * γ (Multiplicative.ofAdd s)) h ∂G.M'.μ = G.M'.I om' Φ h := by
    intro s
    rw [← congrFun (GlobalTheory.ThetaIntegralInv.integral_translate hP.base hPair (γ (Multiplicative.ofAdd s)) Φ (hS Φ hΦ)) h]
    unfold Model.I theta
    congr 1
    funext g
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ₁ (hSo _ hΦ₁) 0
  obtain ⟨C0, k0, hC0⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ (hSo _ hΦ) 0
  have hB1 := ((GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ₁ (hS _ hΦ₁)).1
  have hB0 := ((GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ (hS _ hΦ)).1
  have hcont : ∀ (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Continuous (fun x : UA σ G.V'.J × UA σ G.W.J => theta om' Ψ x.1 x.2) →
      ∀ c : UA σ G.V'.J, Continuous fun g : UA σ G.V'.J => theta om' Ψ (g * c) h := by
    intro Ψ hΨ c
    exact hΨ.comp ((continuous_mul_const c).prodMk continuous_const)
  have hder : ∀ (g : UA σ G.V'.J) (s : ℝ), HasDerivAt (fun t : ℝ => theta om' Φ (g * γ (Multiplicative.ofAdd t)) h)
      (theta om' Φ₁ (g * γ (Multiplicative.ofAdd s)) h) s := by
    intro g s
    have h1 := HasDerivAt.comp_sub_const (x := s) (a := s) (by rw [sub_self]; exact hL1 (g * γ (Multiplicative.ofAdd s)) h)
    have e : (fun t : ℝ => theta om' Φ (g * γ (Multiplicative.ofAdd t)) h) =
        fun t => theta om' Φ (g * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s))) h := by
      funext t
      rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [e]
    exact h1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := G.M'.μ.restrict G.M'.dom)
    (F := fun (s : ℝ) (g : UA σ G.V'.J) => theta om' Φ (g * γ (Multiplicative.ofAdd s)) h)
    (F' := fun (s : ℝ) (g : UA σ G.V'.J) => theta om' Φ₁ (g * γ (Multiplicative.ofAdd s)) h)
    (x₀ := 0) (s := Set.univ) (bound := fun _ => C * (ht h : ℝ) ^ k) Filter.univ_mem
    (Eventually.of_forall fun s => (hcont Φ hB0 _).aestronglyMeasurable)
    (Integrable.mono' (integrable_const (C0 * (ht h : ℝ) ^ k0))
      (hcont Φ hB0 _).aestronglyMeasurable (ae_of_all _ fun g => by
        have e := hC0 (g * γ (Multiplicative.ofAdd 0)) h
        rw [pow_zero, mul_one] at e
        exact e))
    (hcont Φ₁ hB1 _).aestronglyMeasurable
    (ae_of_all _ fun g s _ => by
        have e := hC (g * γ (Multiplicative.ofAdd s)) h
        rw [pow_zero, mul_one] at e
        exact e)
    (integrable_const _)
    (ae_of_all _ fun g s _ => hder g s)
  have key2 := key.2
  simp only [hconst] at key2
  have e0 := key2.unique (hasDerivAt_const (0 : ℝ) (G.M'.I om' Φ h))
  simp only [ofAdd_zero, map_one, mul_one] at e0
  exact e0

end GlobalTheory.ThKLieTriple

end
