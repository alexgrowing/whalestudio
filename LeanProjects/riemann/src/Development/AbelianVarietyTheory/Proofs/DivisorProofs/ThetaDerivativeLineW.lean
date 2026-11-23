import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleRealWeilIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInfinitePlaceApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDerivativeSchwartz

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK
open Filter Topology Metric

noncomputable section
open scoped Classical Matrix

namespace GlobalTheory.ThetaDerivTriple

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pureA_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F ⇑(c • f) g = c • pureA F ⇑f g := by
  funext x
  simp [pureA, mul_assoc]

theorem comm_heisA {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F)) (x y : Fin a' × Fin (a + a') → Af F)
    {Φ : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) :
    om' (1, h) (GlobalTheory.FinHeis.heisA F B.ψ x y Φ) = GlobalTheory.FinHeis.heisA F B.ψ x y (om' (1, h) Φ) := by
  have hs := hT.weil'.1.1.toIsSplitting
  set d := G.M'.co
  set w := d.e.symm ((fun i => GlobalTheory.FinHeis.finA F (x i)), fun i => GlobalTheory.FinHeis.finA F (y i)) with hw
  have hew : d.e w = ((fun i => GlobalTheory.FinHeis.finA F (x i)), fun i => GlobalTheory.FinHeis.finA F (y i)) := d.e.apply_symm_apply _
  have hef : GlobalTheory.FinHeis.finA F 1 • w = w := by
    apply d.e.injective
    rw [map_smul, hew]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) * 0 = 0; simp
      · change (1 : Af F) * x i = x i; simp
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) * 0 = 0; simp
      · change (1 : Af F) * y i = y i; simp
  have hev : evI F (GlobalTheory.FinHeis.finA F 1) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0; exact map_zero _
  have hfix : actB (cA σ) h w = w := by
    have h0 : GlobalTheory.FinHeis.finA F 1 • (mat h - 1) = 0 := hh _ hev
    show w * (mat h)ᵀ = w
    calc w * (mat h)ᵀ = (GlobalTheory.FinHeis.finA F 1 • w) * (mat h - 1 + 1)ᵀ := by rw [hef, sub_add_cancel]
      _ = w * (GlobalTheory.FinHeis.finA F 1 • (mat h - 1))ᵀ + GlobalTheory.FinHeis.finA F 1 • w := by
        rw [Matrix.transpose_add, Matrix.mul_add, Matrix.transpose_one, Matrix.mul_one, Matrix.smul_mul,
          Matrix.transpose_smul, Matrix.mul_smul]
      _ = w := by rw [h0, Matrix.transpose_zero, Matrix.mul_zero, zero_add, hef]
  have himpl := hs.impl h w Φ hΦ
  rw [hfix] at himpl
  have hrho : ∀ Ψ, d.rho B.ψ w Ψ =
      B.ψ (⅟(2 : AF F) * ((fun i => GlobalTheory.FinHeis.finA F (x i)) ⬝ᵥ fun i => GlobalTheory.FinHeis.finA F (y i))) •
        GlobalTheory.FinHeis.heisA F B.ψ x y Ψ := by
    intro Ψ; funext z
    simp only [Darboux.rho, hew, schr, GlobalTheory.FinHeis.heisA, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hrho, hrho] at himpl
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, map_smul] at himpl
  exact smul_right_injective _ (GlobalTheory.ArchFactorFin.addChar_ne_zero _ _) himpl

theorem arch_factor {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (f : SInf F (Fin a' × Fin (a + a'))) : ∃ u : SInf F (Fin a' × Fin (a + a')),
      ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, h) (pureA F f g) = pureA F u g :=
  GlobalTheory.ArchFactorFin.exists_arch_factor_of_comm B.ψ hT.base.std (om' (1, h))
    (fun Φ hΦ => hT.weil'.1.1.toIsSplitting.pres h Φ hΦ) (fun x y Φ hΦ => comm_heisA hT hh x y hΦ) f

theorem orbit_slope {hK : KP} {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W)
    (f : SInf F (Fin a' × Fin (a + a'))) (u : ℝ → SInf F (Fin a' × Fin (a + a')))
    (hu : ∀ t : ℝ, ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, γ (Multiplicative.ofAdd t)) (pureA F f g) = pureA F (u t) g) :
    ∃ u₁ : SInf F (Fin a' × Fin (a + a')), Tendsto (fun t : ℝ => t⁻¹ • (u t - u 0)) (𝓝[≠] 0) (𝓝 u₁) := by
  obtain ⟨c, c', hc0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hK.base G.M' B.ψ X.α (X.α / X.β) om'
    hT.base.cm hT.base.std hT.weil' γ hγ f
  obtain ⟨g, hg, y, hy⟩ := GlobalTheory.OrbitArchSlope.exists_sb_ne_zero F (Fin a' × Fin (a + a'))
  let r : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have hpure : ∀ h : SInf F (Fin a' × Fin (a + a')), pureA F (⇑h) g = tens (evI F) (⇑h) r := fun h => rfl
  have hRest : Rest (evI F) (⇑f) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · let e : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
      have he : evI F e = 0 := by
        show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
        exact map_zero _
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h1 := congrFun (hz e he) i
        have h2 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd h1
        simpa using h2
      show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [hz2 i, add_zero]
    · rw [← hpure]
      exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  have heq : ∀ t, u t = c t := by
    intro t
    have h1 : pureA F (⇑(u t)) g = pureA F (⇑(c t)) g := by
      rw [← hu t g hg, hpure, hpure]
      exact hacts t r hRest
    refine DFunLike.ext _ _ fun x => ?_
    have e := congrFun h1 (fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)))
    simp only [pureA] at e
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    rw [hx] at e
    exact mul_right_cancel₀ hy e
  have hc : u = c := funext heq
  subst hc
  refine ⟨c', ?_⟩
  rw [hc0]
  exact hlim

theorem orbit {hK : KP} {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W)
    {Φ} (hΦ : Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) :
    ∃ (m : ℕ) (φ : Fin m → (Fin a' × Fin (a + a') → Af F) → ℂ) (f : ℝ → Fin m → SInf F (Fin a' × Fin (a + a')))
      (f₁ : Fin m → SInf F (Fin a' × Fin (a + a'))), (∀ i, φ i ∈ SB (Fin a' × Fin (a + a') → Af F)) ∧
      (∀ t : ℝ, om' (1, γ (Multiplicative.ofAdd t)) Φ = ∑ i, pureA F (f t i) (φ i)) ∧ Φ₁ = ∑ i, pureA F (f₁ i) (φ i) ∧
      ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (f t i - f 0 i)) (𝓝[≠] 0) (𝓝 (f₁ i)) := by
  have hsch := GlobalTheory.KDecayProof.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ).2
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hsch
  choose f0 φ hφ hfe using fun i => (g i).2
  choose u hu using fun (t : ℝ) (i : Fin n) => arch_factor hT (hγ.2 (Multiplicative.ofAdd t)) (c i • f0 i)
  have hu' : ∀ i, ∀ t : ℝ, ∀ g' ∈ SB (Fin a' × Fin (a + a') → Af F),
      om' (1, γ (Multiplicative.ofAdd t)) (pureA F (c i • f0 i) g') = pureA F (u t i) g' :=
    fun i t => hu t i
  choose u₁ hu₁ using fun i => orbit_slope (hK := hK) hT hγ (c i • f0 i) (fun t => u t i) (hu' i)
  have hΦe : Φ = ∑ i, pureA F (c i • f0 i) (φ i) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfe i, pureA_smul]
  have horb : ∀ t : ℝ, om' (1, γ (Multiplicative.ofAdd t)) Φ = ∑ i, pureA F (u t i) (φ i) := by
    intro t
    rw [hΦe, map_sum]
    exact Finset.sum_congr rfl fun i _ => hu t i (φ i) (hφ i)
  refine ⟨n, φ, u, u₁, hφ, horb, ?_, hu₁⟩
  funext x
  set y : Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  set z : Fin a' × Fin (a + a') → Af F := fun j => (x j).2
  have hder : ∀ i, HasDerivAt (fun t : ℝ => u t i y) (u₁ i y) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    let ev : SInf F (Fin a' × Fin (a + a')) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)
    have h1 := (ev.continuous.tendsto (u₁ i)).comp (hu₁ i)
    have e2 : ev (u₁ i) = u₁ i y := rfl
    rw [e2] at h1
    refine h1.congr' (Eventually.of_forall fun t => ?_)
    simp [ev, slope_def_module]
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, u t i y * φ i z) (∑ i, u₁ i y * φ i z) 0 :=
    HasDerivAt.fun_sum fun i _ => (hder i).mul_const _
  have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) = fun t => ∑ i, u t i y * φ i z := by
    funext t
    rw [horb, Finset.sum_apply]
    rfl
  have := hd x
  rw [e1] at this
  rw [this.unique hsum, Finset.sum_apply]
  rfl

theorem kernel_deriv (hP : KP) {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W)
    {Φ} (hΦ : Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (Φ₁ : (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) (g h) :
    HasDerivAt (fun t : ℝ => theta om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) g h) (theta om' Φ₁ g h) 0 := by
  obtain ⟨m, φ, f, f₁, hφ, hf, hf₁, hlim⟩ := orbit (hK := hP) hT hγ hΦ Φ₁ hd
  have := GlobalTheory.T.pair_theta_uniform_bound_family hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.KDecayProof.isPair_small hT) m φ f f₁ hφ hlim g h
  rw [← hf₁] at this
  simpa only [hf] using this

theorem hasDerivAt_thetaIntegral_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
      ∀ h, HasDerivAt (fun t : ℝ => G.M'.I om' Φ (h * γ (Multiplicative.ofAdd t))) (G.M'.I om' Φ₁ h) 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hP hT γ hγ Φ hΦ Φ₁ hΦ₁ hd h
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
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
    have h0 := kernel_deriv hP hT hγ hΦ Φ₁ hd g (h * γt t)
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
  have e1 : (fun t : ℝ => G.M'.I om' Φ (h * γ (Multiplicative.ofAdd t))) = fun t => ∫ g, K t g ∂(G.M'.μ.restrict G.M'.dom) := by
    funext t
    rfl
  have e2 : G.M'.I om' Φ₁ h = ∫ g, K' 0 g ∂(G.M'.μ.restrict G.M'.dom) := by
    show ∫ g in G.M'.dom, theta om' Φ₁ g h ∂G.M'.μ = ∫ g, K' 0 g ∂(G.M'.μ.restrict G.M'.dom)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show theta om' Φ₁ g h = theta om' Φ₁ g (h * γt 0)
    rw [hγ0, mul_one]
  rw [e1, e2]
  exact hmain.2

end GlobalTheory.ThetaDerivTriple
