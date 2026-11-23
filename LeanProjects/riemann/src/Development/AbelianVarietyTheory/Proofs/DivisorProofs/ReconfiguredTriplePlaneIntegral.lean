import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

open GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SoPolApprox

open GlobalTheory.ThKSoDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem soLoc_change {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {V : Spc F E a} {V' : Spc F E b} {W₁' : Spc F E (a + b)}
    {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) :
    (reG G₁ V V' W₁').M'.SoLoc B.ψ t = G₁.M'.SoLoc B.ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
    exact ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
  · rintro ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
    exact ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩

theorem so_change {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {V : Spc F E a} {V' : Spc F E b} {W₁' : Spc F E (a + b)} :
    (reG G₁ V V' W₁').M'.So B.ψ B.τ₁ = G₁.M'.So B.ψ B.τ₁ := by
  unfold Model.So
  rw [soLoc_change]
  rfl

theorem continuous_ht {d : ℕ} {J : Matrix (Fin d) (Fin d) E} : Continuous (fun h : UA σ J => (ht h : ℝ)) :=
  NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem theta_add (hPair : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g h) :
    theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add]
  exact thetaSum_add F (hPair.weil.isUSplitting.pres _ _ hΦ) (hPair.weil.isUSplitting.pres _ _ hΨ)

theorem theta_smul (c : ℂ) (Φ : Fn F n d) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul]
  exact thetaSum_smul F c _

open scoped Classical in

theorem exists_approx_theta (hP : KP) (hPair : IsPair B M χX χW om r s r' s') : ∀ Ψ ∈ M.So B.ψ B.τ₁,
    ∃ Ψs : ℕ → Fn F n d, (∀ k, Ψs k ∈ PolData B M ⊓ M.So B.ψ B.τ₁) ∧ ∀ R : ℝ,
      TendstoUniformlyOn (fun k (p : UA σ X.J × UA σ W.J) => theta om (Ψs k) p.1 p.2) (fun p => theta om Ψ p.1 p.2) atTop
        {p | (ht p.2 : ℝ) ≤ R} := by
  intro Ψ hΨ
  have hsch : M.So B.ψ B.τ₁ ≤ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hPair.good _
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := hx
    have hstd := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    have hφ : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
      ⟨isLocallyConstant_finprod_evalV φ h1 hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 hstd⟩
    have hall : ∀ f' : SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ ∈ M.So B.ψ B.τ₁ :=
      fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩
    obtain ⟨C, k, hC⟩ := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair _ hφ hall 0
    have hD := GlobalTheory.PolDense.pol_dense F E σ B n d X W M χX χW om r s r' s' hPair
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hD f)
    refine ⟨fun j => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (u j) φ,
      fun j => ⟨Submodule.subset_span ⟨u j, hu j, φ, h1, h2, rfl⟩, hall _⟩, fun R => ?_⟩
    have hsem : Tendsto (fun j => semK (Fin n × Fin d) k (f - u j)) atTop (𝓝 0) := by
      have hc : Continuous (semK (F := F) (Fin n × Fin d) k) :=
        Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
      have h0 : Tendsto (fun j => f - u j) atTop (𝓝 (f - f)) := tendsto_const_nhds.sub hlim
      rw [sub_self] at h0
      have := (hc.tendsto 0).comp h0
      rwa [map_zero] at this
    have hb : Tendsto (fun j => |C| * semK (Fin n × Fin d) k (f - u j) * |R| ^ k) atTop (𝓝 0) := by
      simpa using (hsem.const_mul |C|).mul_const (|R| ^ k)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hb.eventually (gt_mem_nhds hε)] with j hj p hp
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - u j) φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (u j) φ := by
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.add_apply, SchwartzMap.sub_apply]
      ring
    rw [dist_eq_norm, e, theta_add hPair (hsch (hall _)) (hsch (hall _)), add_sub_cancel_right]
    have h4 := hC (f - u j) p.1 p.2
    rw [pow_zero, mul_one] at h4
    refine lt_of_le_of_lt (h4.trans ?_) hj
    have h5 : 0 ≤ semK (Fin n × Fin d) k (f - u j) := apply_nonneg _ _
    have h6 : (ht p.2 : ℝ) ≤ |R| := le_trans hp (le_abs_self R)
    gcongr
    exact le_abs_self C
  | zero =>
    refine ⟨fun _ => 0, fun _ => Submodule.zero_mem _, fun R => ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by rw [dist_self]; exact hε
  | add x y hx hy ihx ihy =>
    obtain ⟨xs, hxs, hxl⟩ := ihx
    obtain ⟨ys, hys, hyl⟩ := ihy
    refine ⟨fun k => xs k + ys k, fun k => Submodule.add_mem _ (hxs k) (hys k), fun R => ?_⟩
    have := (hxl R).add (hyl R)
    convert this using 1
    · funext k p
      exact theta_add hPair (hsch (hxs k).2) (hsch (hys k).2) _ _
    · funext p
      exact theta_add hPair (hsch hx) (hsch hy) _ _
  | smul c x hx ihx =>
    obtain ⟨xs, hxs, hxl⟩ := ihx
    refine ⟨fun k => c • xs k, fun k => Submodule.smul_mem _ c (hxs k), fun R => ?_⟩
    have := (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (hxl R)
    convert this using 1
    · funext k p
      exact theta_smul c _ _ _
    · funext p
      exact theta_smul c _ _ _

theorem integral_basic (hP : KP) (hPair : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hSo : Φ ∈ M.So B.ψ B.τ₁) :
    M.Conv om Φ ∧ Continuous (M.I om Φ) ∧ ∀ γ ∈ ratU σ W.J, ∀ h, M.I om Φ (γ * h) = M.I om Φ h := by
  have hS : Φ ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hPair.good _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ hS
  obtain ⟨C, k, hC⟩ := soDecay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ hSo 0
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hPair.base hPair.herm hPair.good
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 hv.ne
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · refine Integrable.of_bound (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (C * (ht h : ℝ) ^ k) (Eventually.of_forall fun g => ?_)
    have h1 := hC g h
    rwa [pow_zero, mul_one] at h1
  · have hht : Continuous (fun h : UA σ W.J => (ht h : ℝ)) := continuous_ht
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : SecondCountableTopology (AE F E) := by
      obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
      exact e.secondCountableTopology
    haveI hMat : SecondCountableTopology (Matrix (Fin d) (Fin d) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin d → Fin d → AE F E))
    haveI : SecondCountableTopology (Matrix (Fin d) (Fin d) (AE F E))ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := Matrix (Fin d) (Fin d) (AE F E))).symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin d) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    haveI : SecondCountableTopology (UA σ W.J) :=
      (Topology.IsEmbedding.subtypeVal
        (p := fun x : GL (Fin d) (AE F E) => x ∈ GlobalTheory.WeilM.UG (cA σ) (incM F W.J))).secondCountableTopology
    haveI : FirstCountableTopology (UA σ W.J) :=
      TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    rw [continuous_iff_continuousAt]
    intro h₀
    have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 :=
      hht.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    unfold Model.I
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun g => ?_
      have h1 := hC g h
      rw [pow_zero, mul_one] at h1
      calc ‖theta om Φ g h‖ ≤ C * (ht h : ℝ) ^ k := h1
        _ ≤ max C 0 * (ht h : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh.le _) (le_max_right _ _)
    · exact integrable_const _
    · exact Eventually.of_forall fun g =>
        (hB.1.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e := hB.2.1 1 (one_mem _) γ hγ g h
    rw [one_mul] at e
    exact e

theorem tendstoUniformlyOn_integral {α β : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (S : Set β)
    (fs : ℕ → α → β → ℂ) (f : α → β → ℂ) (hfs : ∀ k, ∀ y ∈ S, Integrable (fun x => fs k x y) μ)
    (hf : ∀ y ∈ S, Integrable (fun x => f x y) μ)
    (hl : ∀ ε > 0, ∀ᶠ k in atTop, ∀ x, ∀ y ∈ S, dist (f x y) (fs k x y) < ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ S, dist (∫ x, f x y ∂μ) (∫ x, fs k x y ∂μ) < ε := by
  intro ε hε
  have hc0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
  filter_upwards [hl (ε / (μ.real Set.univ + 1)) (by positivity)] with k hk y hy
  rw [dist_eq_norm, ← integral_sub (hf y hy) (hfs k y hy)]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / (μ.real Set.univ + 1))
    (Eventually.of_forall fun x => ?_)) ?_
  · rw [← dist_eq_norm]; exact (hk x y hy).le
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith

theorem exists_approx_pair (hP : KP) (hPair : IsPair B M χX χW om r s r' s') (N : Subgroup (UA σ W.J))
    (hN : GlobalTheory.Cusp.Cocompact (ratU σ W.J) N) : ∀ Ψ ∈ M.So B.ψ B.τ₁,
    ∃ Ψs : ℕ → Fn F n d, (∀ k, Ψs k ∈ PolData B M ⊓ M.So B.ψ B.τ₁) ∧ ∀ (μ : Measure N) [IsFiniteMeasure μ] (h : UA σ W.J),
      Tendsto (fun k => ∫ u, M.I om (Ψs k) (u.1 * h) ∂μ) atTop (𝓝 (∫ u, M.I om Ψ (u.1 * h) ∂μ)) := by
  intro Ψ hΨ
  obtain ⟨Ψs, hΨs, hl⟩ := exists_approx_theta hP hPair Ψ hΨ
  refine ⟨Ψs, hΨs, fun μ _ h => ?_⟩
  obtain ⟨K, hK, hKc⟩ := hN
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hPair.base hPair.herm hPair.good
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 hv.ne
  have hm : Continuous fun u : N => u.1 * h := continuous_subtype_val.mul continuous_const
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_ht.comp hm).continuousOn
  have hred : ∀ u : N, ∃ k ∈ K, ∀ Φ ∈ M.So B.ψ B.τ₁, M.I om Φ (u.1 * h) = M.I om Φ (k.1 * h) := by
    intro u
    obtain ⟨γ, hγ, hγu⟩ := hKc u
    refine ⟨γ * u, hγu, fun Φ hΦ => ?_⟩
    rw [Subgroup.coe_mul, mul_assoc]
    exact ((integral_basic hP hPair hΦ).2.2 γ.1 (Subgroup.mem_subgroupOf.1 hγ) _).symm
  have hint : ∀ Φ ∈ M.So B.ψ B.τ₁, Integrable (fun u : N => M.I om Φ (u.1 * h)) μ := by
    intro Φ hΦ
    have hc : Continuous fun u : N => M.I om Φ (u.1 * h) := (integral_basic hP hPair hΦ).2.1.comp hm
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    refine Integrable.of_bound hc.aestronglyMeasurable D (Eventually.of_forall fun u => ?_)
    obtain ⟨k, hk, e⟩ := hred u
    rw [e Φ hΦ]; exact hD k hk
  have h1 := tendstoUniformlyOn_integral (M.μ.restrict M.dom) {y : UA σ W.J | (ht y : ℝ) ≤ R}
    (fun k x y => theta om (Ψs k) x y) (fun x y => theta om Ψ x y)
    (fun k y _ => (integral_basic hP hPair (hΨs k).2).1 y) (fun y _ => (integral_basic hP hPair hΨ).1 y)
    (fun ε hε => by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hl R) ε hε] with k hk x y hy
      exact hk (x, y) hy)
  have h2 := tendstoUniformlyOn_integral μ (Set.univ : Set Unit)
    (fun k u _ => M.I om (Ψs k) (u.1 * h)) (fun u _ => M.I om Ψ (u.1 * h))
    (fun k _ _ => hint _ (hΨs k).2) (fun _ _ => hint _ hΨ)
    (fun ε hε => by
      filter_upwards [h1 ε hε] with k hk u _ _
      obtain ⟨κ, hκ, e⟩ := hred u
      rw [e _ hΨ, e _ (hΨs k).2]
      exact hk (κ.1 * h) ((le_abs_self _).trans (hR κ hκ)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h2 ε hε] with k hk
  rw [dist_comm]
  exact hk () trivial

theorem approx_pol : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G₁ : Geo σ a b) (X : Chars F E) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ Ψ ∈ G₁.M'.So B.ψ B.τ₁, ∃ Ψs : ℕ → Fn F b (a + b), (∀ k, Ψs k ∈ PolData B (reG G₁ V V' W₁').M' ⊓ G₁.M'.So B.ψ B.τ₁) ∧
      ∀ (μ : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ.IsHaarMeasure →
        IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ → μ 𝓕 = 1 → ∀ h,
        Tendsto (fun k => ∫ u in 𝓕, G₁.M'.I om₁' (Ψs k) (u.1 * h) ∂μ) atTop (𝓝 (∫ u in 𝓕, G₁.M'.I om₁' Ψ (u.1 * h) ∂μ)) := by
  intro hKP F E _ _ _ _ _ σ B a b G₁ X om₁ om₁' _ V V' W₁' hT' e W₂ H₂ i₀ i₁ hH Ψ hΨ
  have hN := GlobalTheory.UnipCocompact.cocompact_unip F E σ B a b (reG G₁ V V' W₁') X om₁ om₁' hT' e W₂ H₂ i₀ i₁ hH
  obtain ⟨Ψs, hΨs, hl⟩ := exists_approx_pair hKP (GlobalTheory.ThKContSmall.isPair_small hT') _ hN Ψ
    (by rw [so_change (G₁ := G₁) (V := V) (V' := V') (W₁' := W₁')]; exact hΨ)
  refine ⟨Ψs, fun k => ?_, fun μ 𝓕 _ _ h1 h => ?_⟩
  · rw [← so_change (G₁ := G₁) (V := V) (V' := V') (W₁' := W₁')]
    exact hΨs k
  · haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
    exact @hl (μ.restrict 𝓕) this h

end GlobalTheory.SoPolApprox

end
