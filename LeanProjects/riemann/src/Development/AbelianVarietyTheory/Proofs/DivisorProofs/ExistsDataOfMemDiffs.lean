import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaLiftNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetSmoothModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftAdaptedInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CtMulLeftUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionUnipotentLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSmallUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftAdaptedGrowthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.DescB.CuspDiff

theorem levi_mul_inv_mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {h₁ : UA σ W₁.J} {m m' : UA σ W.J}
    (hm : IsLevi (W₁ := W₁) H' 1 h₁ m) (hm' : IsLevi (W₁ := W₁) H' 1 h₁ m') : m * m'⁻¹ ∈ unip σ W H' := by
  have hmul : mat (m * m'⁻¹) * mat m' = mat m := by
    have : mat (m * m'⁻¹ * m') = mat (m * m'⁻¹) * mat m' := rfl
    rw [← this, inv_mul_cancel_right]
  have h1 : mat h₁ * mat h₁⁻¹ = 1 := by
    have : mat (h₁ * h₁⁻¹) = mat h₁ * mat h₁⁻¹ := rfl
    rw [← this, mul_inv_cancel]; rfl
  refine Subgroup.subset_closure ⟨?_, fun z => ⟨0, ?_⟩⟩
  · have e1 := hm.1
    have e2 := hm'.1
    simp only [Units.val_one, one_smul] at e1 e2
    calc mat (m * m'⁻¹) *ᵥ incV F H'.x = mat (m * m'⁻¹) *ᵥ (mat m' *ᵥ incV F H'.x) := by rw [e2]
      _ = incV F H'.x := by rw [Matrix.mulVec_mulVec, hmul, e1]
  · have e : mat (m * m'⁻¹) * incM F H'.ι = incM F H'.ι := by
      calc mat (m * m'⁻¹) * incM F H'.ι = mat (m * m'⁻¹) * (incM F H'.ι * mat h₁) * mat h₁⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
        _ = incM F H'.ι := by
            rw [← hm'.2.2, ← Matrix.mul_assoc, hmul, hm.2.2, Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, e, zero_smul, add_zero]

theorem exists_data_of_mem_diffs (hK : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf) {c : ℂ}
    {f : UA σ G.W.J → ℂ} (hf : f ∈ Diffs B G X om om' R Rf c) :
    ∃ Φ ∈ PolData B G.M, ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      G.M.I om Φ ∈ thetaSpanV B G X om R Rf ∧ G.M'.I om' Φ' ∈ thetaSpanV' B G X om' R Rf ∧
      f = fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h := by
  have hT := hM.triple
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hW := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  have hS := GlobalTheory.ThK.SqIntCont.polData_le_schA (B := B) hT.geo.hM
  have lin := GlobalTheory.T.matched_pair_theta_local_global hK F E σ B a a' G X om om' R Rf hM
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Φ, Φ', hΦ', hm, rfl⟩ := hf
    obtain ⟨h1, h2⟩ := GlobalTheory.ThKOrthCusp.polData_of_polMatch hm
    exact ⟨Φ, h1, Φ', ⟨h2, hΦ'⟩, Submodule.subset_span ⟨Φ, Φ', hΦ', hm, rfl⟩,
      Submodule.subset_span ⟨Φ, Φ', hΦ', hm, rfl⟩, rfl⟩
  | zero =>
    refine ⟨(0 : ℂ) • 0, Submodule.smul_mem _ _ (Submodule.zero_mem _), (0 : ℂ) • 0,
      Submodule.smul_mem _ _ (Submodule.zero_mem _), ?_⟩
    rw [SpanVSplit.thetaInt_smul, SpanVSplit.thetaInt_smul, zero_smul, zero_smul]
    refine ⟨Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
    funext h; simp
  | add f g _ _ ihf ihg =>
    obtain ⟨Φ, hΦ, Φ', hΦ', s1, s1', rfl⟩ := ihf
    obtain ⟨Ψ, hΨ, Ψ', hΨ', s2, s2', rfl⟩ := ihg
    have e1 := SpanVSplit.thetaInt_add G.M om (IsUWeilPair.isUSplitting hT.weil).pres (hS hΦ) (hS hΨ)
      (hW.1 Φ (hS hΦ)).1 (hW.1 Ψ (hS hΨ)).1
    have e2 := lin Φ' hΦ' Ψ' hΨ' 1
    rw [one_smul, one_smul] at e2
    refine ⟨Φ + Ψ, Submodule.add_mem _ hΦ hΨ, Φ' + Ψ', Submodule.add_mem _ hΦ' hΨ', ?_⟩
    rw [e1, e2]
    refine ⟨Submodule.add_mem _ s1 s2, Submodule.add_mem _ s1' s2', ?_⟩
    funext h; simp only [Pi.add_apply]; ring
  | smul z f _ ih =>
    obtain ⟨Φ, hΦ, Φ', hΦ', s1, s1', rfl⟩ := ih
    refine ⟨z • Φ, Submodule.smul_mem _ _ hΦ, z • Φ', Submodule.smul_mem _ _ hΦ', ?_⟩
    rw [SpanVSplit.thetaInt_smul, SpanVSplit.thetaInt_smul]
    refine ⟨Submodule.smul_mem _ _ s1, Submodule.smul_mem _ _ s1', ?_⟩
    funext h; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem isCT_zero (hK : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf)
    {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) {c : ℂ}
    (hβ : BetaZero W₁ H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c))
    (hα : alphaSpan W₁ H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (finK σ G.W B.emb) (Diffs B G X om om' R Rf c) = ⊥)
    {f : UA σ G.W.J → ℂ} (hf : f ∈ Diffs B G X om om' R Rf c) : IsCT H' f 0 := by
  have hT := hM.triple
  obtain ⟨Φ, hΦ, Φ', hΦ', s1, s1', hfe⟩ := exists_data_of_mem_diffs hK hM hf
  obtain ⟨hsV, hsV'⟩ := GlobalTheory.T.split_existence hK F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨⟨ga, gb⟩, (hs : Split2 W₁ H' X (G.M.I om Φ) ga gb), -⟩ := hsV Φ hΦ
  obtain ⟨⟨ga', gb'⟩, (hs' : Split2 W₁ H' X (G.M'.I om' ((-c) • Φ')) ga' gb'), -⟩ :=
    hsV' ((-c) • Φ') (Submodule.smul_mem _ _ hΦ')
  rw [SpanVSplit.thetaInt_smul] at hs'
  have hadd := GlobalTheory.T.theta_lift_adapted_growth hK F E σ B a a' G X om om' R Rf hM d₁ W₁ H' i₀ i₁ hH _ s1 _ (Submodule.smul_mem _ (-c) s1')
    _ _ hs.1 hs'.1
  have e : G.M.I om Φ + (-c) • G.M'.I om' Φ' = f := by
    rw [hfe]; funext h; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e] at hadd
  have hsp : SplitZ W₁ H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) f (ga + ga') (gb + gb') := by
    refine ⟨by rw [add_add_add_comm]; exact hadd, fun t m hm h => ?_, fun t m hm h => ?_⟩
    · simp only [Pi.add_apply]
      rw [hs.2.1 t m hm h, hs'.2.1 t m hm h]; ring
    · simp only [Pi.add_apply]
      rw [hs.2.2 t m hm h, hs'.2.2 t m hm h]; ring
  have hb0 := hβ f hf _ _ hsp
  have hct : IsCT H' f (ga + ga') := by
    have := hsp.1
    rwa [hb0, add_zero] at this
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1, -⟩ := GlobalTheory.T.unipotent_haar_fundamental_domain_exists F E σ B a a' G X om om' hK hT d₁ W₁ H' i₀ i₁ hH
  have hinv := GlobalTheory.CTInv.ct_mul_left_unip F E σ (a + a') d₁ G.W H' f _ hct ⟨μ, 𝓕, hμ, h𝓕, h1⟩
  have hex := GlobalTheory.T.exists_levi_element_small_unitary F E σ B (a + a') G.W _ _ d₁ W₁ H' i₀ i₁ hT.base.cm hT.geo.hW hH
  have huniq : ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → ∀ k ∈ finK σ G.W B.emb, (ga + ga') (m * k) = 0 := by
    intro h₁ m hm k hk
    choose lv hlv using hex
    have hmem : (fun x => (ga + ga') (lv x * k)) ∈
        alphaSpan W₁ H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (finK σ G.W B.emb) (Diffs B G X om om' R Rf c) := by
      refine Submodule.subset_span ⟨f, hf, _, _, hsp, k, hk, fun x => ⟨lv x, hlv x⟩, fun x m' hm' => ?_⟩
      have := hinv _ (levi_mul_inv_mem_unip (hlv x) hm') (m' * k)
      rw [← this]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [hα, Submodule.mem_bot] at hmem
    have h0 : (ga + ga') (lv h₁ * k) = 0 := congrFun hmem h₁
    have := hinv _ (levi_mul_inv_mem_unip hm (hlv h₁)) (lv h₁ * k)
    rw [h0] at this
    rw [← this]
    simp only [mul_assoc, inv_mul_cancel_left]
  have ha0 : ga + ga' = 0 := by
    funext g
    obtain ⟨n, hn, t, m₁, hm₁, h₁, m₂, hm₂, k, hk, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_unipotent_levi F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH g
    have hassoc : n * m₁ * m₂ * k = n * (m₁ * (m₂ * k)) := by simp only [mul_assoc]
    rw [hassoc, hinv n hn, hsp.2.1 t m₁ hm₁, huniq h₁ m₂ hm₂ k hk, mul_zero, Pi.zero_apply]
  rwa [ha0] at hct

theorem decay (hK : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) (c : ℂ)
    {Φ : Fn F a (a + a')} (hΦd : Φ ∈ PolData B G.M) {Φ' : Fn F a' (a + a')}
    (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    (hCT : IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0) (N : ℕ) :
    ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C := by
  have h : IsCMExt F E σ := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨c₁, hc₁, hc₁σ⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ h
  have hJ₁ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B (a + a') G.W _ _ hT.geo.hW c₁ hc₁ hc₁σ
  obtain ⟨K, hKm, hAV, hAV'⟩ := GlobalTheory.T.max_compact_pol_data_pair F E σ hσ B a a' G X om om' hK hT c₁ hc₁ hc₁σ Φ hΦd Φ' hΦ'
  have hA : IsAut σ (c₁ • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc₁).symm x) -
      c * G.M'.I om' Φ' ((toGAd hσ G.W.J hc₁).symm x)) :=
    GlobalTheory.StdPar.isAutOn_empty.1 (GlobalTheory.T.automorphic_sub_scalar_mul F E σ (a + a') _ 0 (0 : Matrix (Fin (a + a')) (Fin 0) E) 0 ∅ K _ _ c
      (GlobalTheory.StdPar.isAutOn_empty.2 hAV) (GlobalTheory.StdPar.isAutOn_empty.2 hAV'))
  obtain ⟨hx0, hxiso, hct⟩ := GlobalTheory.T.constant_term_nonzero_vector F E σ hσ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.geo.hW hH c₁ hc₁ _ hCT
  have hcusp := GlobalTheory.ThKOrthCusp.core h hJ₁ hK.automorphicFormsUnitary.2 hKm hA
    (fun x hx hxi => GlobalTheory.T.constant_term_isotropic_vectors F E σ h (a + a') _ hJ₁ _ hA.mod.left _ x hx0 hxiso hx hxi hct)
    (fun r Xf Yf hW S hS => by
      have h1 := GlobalTheory.T.pol_data_witt_frame_scaled F E σ hσ B a a' G X om om' hK hT c₁ hc₁ hc₁σ Φ hΦd r Xf Yf hW K hKm hAV S hS
      have h2 := GlobalTheory.T.pol_data_so_witt_frame F E σ hσ B a a' G X om om' hK hT c₁ hc₁ hc₁σ Φ' hΦ' r Xf Yf hW K hKm hAV' S hS
      have := GlobalTheory.T.automorphic_linear_combination_const F E σ h (a + a') _ hJ₁ r Xf Yf hW K S _ _ 0 0 c (GlobalTheory.StdPar.isAutOn_empty.2 hAV)
        (GlobalTheory.StdPar.isAutOn_empty.2 hAV') h1 h2
      convert this using 1
      funext x; simp)
  refine GlobalTheory.SiegelSet.rapidDecay_qht hK.siegelSetUnitary F E σ h _ G.W.J c₁ hc₁ hJ₁
    (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) _ (fun g g' e => ?_) hA.mod hcusp N
  have : (toGAd hσ G.W.J hc₁).symm g' = g := Subtype.ext e.symm
  simp only [this]

end GlobalTheory.ThK.DescB.CuspDiff
