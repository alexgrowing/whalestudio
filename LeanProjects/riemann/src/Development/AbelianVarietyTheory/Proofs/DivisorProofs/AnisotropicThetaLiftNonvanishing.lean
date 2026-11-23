import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalScaleHermitianFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolDataPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataWittFrameScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermNonzeroVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIsotropicVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsExtendWittStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicLinearCombinationConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMulStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThKOrthCusp

theorem zeroComp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)} {K : Subgroup (GAd σ J)}
    {φ : GAd σ J → ℂ} (h : GlobalTheory.StdPar.IsConstAlong σ J X S φ 0) : GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ 0 := by
  refine ⟨⟨GlobalTheory.StdPar.isAutOn_const σ J X Y S K 0, fun S' _ => GlobalTheory.StdPar.isConstAlong_const σ J X S' 0⟩, 0, h,
    fun ψ _ μ 𝓕 _ _ g g' => ⟨?_, ?_, ?_⟩⟩ <;> simp

theorem polData_of_polMatch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {Φ Φ'}
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ GlobalTheory.ThK.PolData B G.M ∧ Φ' ∈ GlobalTheory.ThK.PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, rfl, rfl, -⟩ := h
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩,
    Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (hj j).2.1, ?_, rfl⟩⟩
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hi i).2.2 v hT))
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hj j).2.2 v hT))

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (hL : GlobalTheory.Published.LanglandsLemmaUnitary) {K : Subgroup (GAd σ J)} (hK : IsMaxCpt σ J K) {φ : GAd σ J → ℂ}
    (hφ : IsAut σ J K φ)
    (hline : ∀ x : Matrix (Fin n) (Fin 1) E, x ≠ 0 → Formalism.UG.cT (σ : E →+* E) x * J * x = 0 → IsConstTerm σ J x φ 0)
    (hblk : ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ S : Finset (Fin r),
      ¬ (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ 0) :
    IsCuspidal σ J φ := by
  intro r C ⟨hr, hind, hiso⟩ μ 𝓕 hμ h𝓕 g
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm, X, Y, hW, hC⟩ := GlobalTheory.T.isotropic_columns_extend_witt F E σ h n J hJ r C hind hiso
  have hm1 : 1 ≤ m := by omega
  have hAut : GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K φ := GlobalTheory.StdPar.isAutOn_empty.2 hφ
  have hLL := hL F E σ h n J hJ m X Y hW K hK ∅ φ hAut
  obtain ⟨ψ, hψ, -⟩ := hLL.1 ∅ le_rfl
  have hψc : GlobalTheory.StdPar.IsCuspOn σ J X Y ∅ K ψ := hψ.1
  have hiso0 := isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ hm1
  have hx0 : X.submatrix id (Fin.castLE hm1) ≠ 0 := fun e => by
    have := hiso0.1.ne_zero (0 : Fin 1)
    exact this (by rw [e]; rfl)
  have hline0 : IsConstTerm σ J (X.submatrix id (Fin.castLE hm1)) φ 0 := hline _ hx0 hiso0.2
  have h0 : ∀ S : Finset (Fin m), S.Nonempty → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ 0 := by
    intro S hS
    by_cases hi : ∀ k ∈ S, ∀ i ≤ k, i ∈ S
    · obtain ⟨k, hk⟩ := hS
      have h0S : (⟨0, by omega⟩ : Fin m) ∈ S := hi k hk _ (show (⟨0, by omega⟩ : Fin m) ≤ k from Nat.zero_le _)
      apply zeroComp
      refine GlobalTheory.T.constant_term_along_subset F E σ h n J hJ m X Y hW φ hφ.mod.cont hφ.mod.left S {⟨0, by omega⟩}
        (Finset.singleton_subset_iff.2 h0S) ?_
      rw [GlobalTheory.StdPar.isConstAlong_singleton hW]
      exact hline0
    · exact hblk m X Y hW S hi
  have hψ0 : ∀ S : Finset (Fin m), S.Nonempty → GlobalTheory.StdPar.IsCuspComp σ J X Y S K ψ 0 := fun S hS =>
    zeroComp (hψc.2 S (Finset.empty_ssubset.2 hS))
  have hψself : GlobalTheory.StdPar.IsCuspComp σ J X Y ∅ K ψ ψ := GlobalTheory.StdPar.isCuspComp_self hL h hJ hW hK hψc
  have hdiff : ∀ S : Finset (Fin m), GlobalTheory.StdPar.IsCuspComp σ J X Y S K (fun g => φ g - 1 * ψ g) 0 := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | hS
    · have := GlobalTheory.T.automorphic_linear_combination_const F E σ h n J hJ m X Y hW K ∅ φ ψ ψ ψ 1 hAut hψc.1 hψ hψself
      convert this using 1
      funext x; simp
    · have := GlobalTheory.T.automorphic_linear_combination_const F E σ h n J hJ m X Y hW K S φ ψ 0 0 1 hAut hψc.1 (h0 S hS) (hψ0 S hS)
      convert this using 1
      funext x; simp
  have hAutD := GlobalTheory.T.automorphic_sub_scalar_mul F E σ n J m X Y ∅ K φ ψ 1 hAut hψc.1
  have hzero := (hL F E σ h n J hJ m X Y hW K hK ∅ _ hAutD).2.1 fun S _ => hdiff S
  have hφψ : φ = ψ := funext fun x => by
    have := congrFun hzero x
    simpa [sub_eq_zero] using this
  have hk : (∅ : Finset (Fin m)) ⊂ {(⟨r, hm⟩ : Fin m)} := Finset.empty_ssubset.2 (Finset.singleton_nonempty _)
  have hct : GlobalTheory.StdPar.IsConstAlong σ J X {(⟨r, hm⟩ : Fin m)} ψ 0 := hψc.2 _ hk
  obtain rfl := hφψ
  rw [GlobalTheory.StdPar.isConstAlong_singleton hW] at hct
  subst hC
  haveI := hμ
  have hC' : IsIsoCols σ J (GlobalTheory.StdPar.initCols X ⟨r, hm⟩) := ⟨hind, hiso⟩
  haveI := locallyCompact_unipRad h hJ hC'
  have hco := cocompact_unipRad h hJ hC'
  have h1 : μ 𝓕 ≠ ⊤ := hco.measure_ne_top h𝓕
  have h0' : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne _)
  have hν : ((μ 𝓕)⁻¹ • μ).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0')
  have hν𝓕 : IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (GlobalTheory.StdPar.initCols X ⟨r, hm⟩))) 𝓕 ((μ 𝓕)⁻¹ • μ) :=
    h𝓕.mono Measure.smul_absolutelyContinuous
  have hν1 : ((μ 𝓕)⁻¹ • μ) 𝓕 = 1 := by simp [ENNReal.inv_mul_cancel h0' h1]
  have := hct _ 𝓕 hν hν𝓕 hν1 g
  rw [Measure.restrict_smul, integral_smul_measure] at this
  have hpos : ((μ 𝓕)⁻¹).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 h1, ENNReal.inv_ne_top.2 h0'⟩
  exact (smul_eq_zero.1 this.symm).resolve_left hpos

theorem cusp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
        (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
        GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • G.W.J.map σ) φ' := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hprop Φ Φ' hΦ' hPM hCT c₀ hc₀ φ' hφ'
  have h : IsCMExt F E σ := hM.triple.base.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨c₁, hc₁, hc₁σ⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ h
  have hJ₁ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B (a + a') G.W _ _ hM.triple.geo.hW c₁ hc₁ hc₁σ
  obtain ⟨hΦd, hΦ'd⟩ := polData_of_polMatch hPM
  obtain ⟨K, hK, hAV, hAV'⟩ := GlobalTheory.T.max_compact_pol_data_pair F E σ hσ B a a' G X om om' hKP hM.triple c₁ hc₁ hc₁σ Φ hΦd Φ' ⟨hΦ'd, hΦ'⟩
  have hA : IsAut σ (c₁ • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc₁).symm x) -
      c * G.M'.I om' Φ' ((toGAd hσ G.W.J hc₁).symm x)) :=
    GlobalTheory.StdPar.isAutOn_empty.1 (GlobalTheory.T.automorphic_sub_scalar_mul F E σ (a + a') _ 0 (0 : Matrix (Fin (a + a')) (Fin 0) E) 0 ∅ K _ _ c
      (GlobalTheory.StdPar.isAutOn_empty.2 hAV) (GlobalTheory.StdPar.isAutOn_empty.2 hAV'))
  obtain ⟨hx0, hxiso, hct⟩ := GlobalTheory.T.constant_term_nonzero_vector F E σ hσ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hM.triple.geo.hW hH' c₁ hc₁ _ hCT
  have hcusp := core h hJ₁ hKP.automorphicFormsUnitary.2 hK hA
    (fun x hx hxi => GlobalTheory.T.constant_term_isotropic_vectors F E σ h (a + a') _ hJ₁ _ hA.mod.left _ x hx0 hxiso hx hxi hct)
    (fun r Xf Yf hW S hS => by
      have h1 := GlobalTheory.T.pol_data_witt_frame_scaled F E σ hσ B a a' G X om om' hKP hM.triple c₁ hc₁ hc₁σ Φ hΦd r Xf Yf hW K hK hAV S hS
      have h2 := GlobalTheory.T.pol_data_so_witt_frame F E σ hσ B a a' G X om om' hKP hM.triple c₁ hc₁ hc₁σ Φ' ⟨hΦ'd, hΦ'⟩ r Xf Yf hW K hK hAV' S hS
      have := GlobalTheory.T.automorphic_linear_combination_const F E σ h (a + a') _ hJ₁ r Xf Yf hW K S _ _ 0 0 c (GlobalTheory.StdPar.isAutOn_empty.2 hAV)
        (GlobalTheory.StdPar.isAutOn_empty.2 hAV') h1 h2
      convert this using 1
      funext x; simp)
  have he : c₀ • G.W.J.map σ = (c₀ / c₁) • (c₁ • G.W.J.map σ) := by rw [smul_smul, div_mul_cancel₀ _ hc₁]
  have hφ₁ : ∀ (g : GAd σ (c₁ • G.W.J.map σ)) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 →
      φ' g' = G.M.I om Φ ((toGAd hσ G.W.J hc₁).symm g) - c * G.M'.I om' Φ' ((toGAd hσ G.W.J hc₁).symm g) :=
    fun g g' hg => hφ' _ g' hg
  exact GlobalTheory.T.cuspidal_scale_hermitian_form F E σ (a + a') (c₁ • G.W.J.map σ) (c₀ • G.W.J.map σ) (c₀ / c₁) (div_ne_zero hc₀ hc₁) he
    (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc₁).symm x) - c * G.M'.I om' Φ' ((toGAd hσ G.W.J hc₁).symm x)) φ' hφ₁ hcusp

end GlobalTheory.ThKOrthCusp
