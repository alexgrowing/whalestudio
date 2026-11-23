import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.ThK.LiftContA

theorem sum_pure_mem_polData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F)) {m : ℕ}
    (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ PolData B M := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (h i).1, φ i, (h i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
  by_contra hT
  exact hv ((h i).2.2 v hT)

theorem continuous_thLift_diff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁, ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ₁ Φ₁' →
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
        Continuous (thLift om' Φ₁' μ 𝓕 (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH c hsplit Φ Φ' hΦ' hPM hct hdec
    Φ₁ Φ₁' hΦ₁' hPM₁ μ 𝓕 hμ h𝓕
  have hT := hM.triple
  obtain ⟨P, P'⟩ := GlobalTheory.ThK.Check.isPair_of_isTriple hT
  have hW := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  have hW' := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P'
    (Or.inr (by rw [hq]; exact Nat.zero_min _))

  have hfc : Continuous (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) := by
    obtain ⟨T, -, m, m', u, φ, u', φ', hu, hu', rfl, rfl, -⟩ := hPM
    have hS : ∑ i, pure (u i) (φ i) ∈ schA F (Fin a × Fin (a + a')) :=
      GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM (sum_pure_mem_polData G.M T u φ hu)
    have hS' : ∑ j, pure (u' j) (φ' j) ∈ schA F (Fin a' × Fin (a + a')) :=
      GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM' (sum_pure_mem_polData G.M' T u' φ' hu')
    have hc : Continuous (G.M.I om (∑ i, pure (u i) (φ i))) :=
      GlobalTheory.ThK.SqIntCont.continuous_I G.M om hT.weil.2.2 (IsUWeilPair.isUSplitting hT.weil).pres
        (fun Ψ hΨ => (hW.1 Ψ hΨ).1) hW.2 hS
    have hc' : Continuous (G.M'.I om' (∑ j, pure (u' j) (φ' j))) :=
      GlobalTheory.ThK.SqIntCont.continuous_I G.M' om' hT.weil'.2.2 (IsUWeilPair.isUSplitting hT.weil').pres
        (fun Ψ hΨ => (hW'.1 Ψ hΨ).1) hW'.2 hS'
    exact hc.sub (continuous_const.mul hc')

  have hS₁ : Φ₁' ∈ schA F (Fin a' × Fin (a + a')) := by
    obtain ⟨T, -, m, m', u, φ, u', φ', -, hu', -, rfl, -⟩ := hPM₁
    exact GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM' (sum_pure_mem_polData G.M' T u' φ' hu')
  obtain ⟨hjc, hinv, C, k, hCk⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P').1
    Φ₁' hS₁

  have hq' : ∀ g h, ‖theta om' Φ₁' g h‖ ≤ |C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
    intro g h
    have hb : ∀ h, ‖theta om' Φ₁' g h‖ ≤ (|C| * (ht g : ℝ) ^ k) * (ht h : ℝ) ^ k := fun h => by
      refine (hCk g h).trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (by positivity)
    have hi : ∀ γ ∈ ratU σ G.W.J, ∀ x, theta om' Φ₁' g (γ * x) = theta om' Φ₁' g x := fun γ hγ x => by
      simpa using hinv 1 (one_mem _) γ hγ g x
    have := GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := fun h => theta om' Φ₁' g h) hi hb h
    rwa [max_eq_left (by positivity)] at this
  obtain ⟨Cf, hCf⟩ := hdec k

  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hd := GlobalTheory.ThK.DescB.Nondeg.det_ne_zero_of_cartan B G.W hT.geo.hW.cartan
  obtain ⟨c₀, hc₀, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hT.geo.hW.skew hd hc₀ hcs
  haveI := hμ
  have hfin := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hKP.siegelSetUnitary hcm hc₀ hJ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : FirstCountableTopology (UA σ G.V'.J) := by
    have heq : UG (cA σ) (incM F G.V'.J) = HR (AF F) σ ((1 : E) • G.V'.J.map σ) :=
      GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.V'.J) hσ one_ne_zero
    let e : UA σ G.V'.J ≃* GAd σ ((1 : E) • G.V'.J.map σ) := MulEquiv.subgroupCongr heq
    have he : Continuous e := continuous_subtype_val.subtype_mk _
    have hind : Topology.IsInducing e :=
      Topology.IsInducing.of_comp he continuous_subtype_val Topology.IsInducing.subtypeVal
    have h2 : SecondCountableTopology (UA σ G.V'.J) := hind.secondCountableTopology
    exact @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ h2
  have hht : Continuous fun g : UA σ G.V'.J => (ht g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  rw [continuous_iff_continuousAt]
  intro g₀
  have hnear : ∀ᶠ g in 𝓝 g₀, (ht g : ℝ) ≤ (ht g₀ : ℝ) + 1 :=
    (hht.continuousAt.eventually (gt_mem_nhds (lt_add_one (ht g₀ : ℝ)))).mono fun g hg => hg.le
  refine continuousAt_of_dominated (bound := fun _ => |C| * ((ht g₀ : ℝ) + 1) ^ k * Cf) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun g =>
      (hfc.mul (Complex.continuous_conj.comp (hjc.comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · refine hnear.mono fun g hg => Eventually.of_forall fun h => ?_
    rw [norm_mul, Complex.norm_conj]
    have hk : (ht g : ℝ) ^ k ≤ ((ht g₀ : ℝ) + 1) ^ k := pow_le_pow_left₀ (by positivity) hg k
    calc ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * ‖theta om' Φ₁' g h‖
        ≤ ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (|C| * ((ht g₀ : ℝ) + 1) ^ k * (qht h : ℝ) ^ k) := by
          refine mul_le_mul_of_nonneg_left ((hq' g h).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (abs_nonneg C)) (by positivity)
      _ = |C| * ((ht g₀ : ℝ) + 1) ^ k * (‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ k) := by ring
      _ ≤ |C| * ((ht g₀ : ℝ) + 1) ^ k * Cf := mul_le_mul_of_nonneg_left (hCf h) (by positivity)
  · exact Eventually.of_forall fun h =>
      (continuous_const.mul (Complex.continuous_conj.comp (hjc.comp (continuous_id.prodMk continuous_const)))).continuousAt

end GlobalTheory.ThK.LiftContA
