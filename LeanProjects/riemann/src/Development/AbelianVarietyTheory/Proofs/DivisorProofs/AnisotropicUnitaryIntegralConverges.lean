import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualThetaConvergenceAnisotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.LiftContDef

theorem continuous_setIntegral_cocompact {Gr P : Type} [Group Gr] [TopologicalSpace Gr] [IsTopologicalGroup Gr]
    [MeasurableSpace Gr] [BorelSpace Gr] [TopologicalSpace P] (Γ : Subgroup Gr) [Countable Γ] (μ : Measure Gr)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set Gr) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (hC : IsCompact C) (hcov : ∀ h : Gr, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : Gr → P → ℂ)
    (hK : Continuous fun z : Gr × P => K z.1 z.2) (hinv : ∀ γ ∈ Γ, ∀ g p, K (γ * g) p = K g p) :
    Continuous fun p => ∫ g in 𝓕, K g p ∂μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 < ⊤ := hle.trans_lt hC.measure_lt_top
  have hint : ∀ p, IntegrableOn (fun g => K g p) 𝓕 μ := fun p => by
    have hF : Continuous fun g => K g p := hK.comp (continuous_id.prodMk continuous_const)
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM c hc
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have hδ : 0 < ε / (μ.real 𝓕 + 1) := by positivity
  have hcl : ∀ᶠ p in 𝓝 p₀, ∀ g ∈ C, ‖K g p - K g p₀‖ < ε / (μ.real 𝓕 + 1) := by
    refine hC.eventually_forall_of_forall_eventually
      (P := fun p g => ‖K g p - K g p₀‖ < ε / (μ.real 𝓕 + 1)) fun g _ => ?_
    have h1 : Continuous fun z : P × Gr => K z.2 z.1 := hK.comp (continuous_snd.prodMk continuous_fst)
    have h2 : Continuous fun z : P × Gr => K z.2 p₀ := hK.comp (continuous_snd.prodMk continuous_const)
    have hc : Continuous fun z : P × Gr => ‖K z.2 z.1 - K z.2 p₀‖ := (h1.sub h2).norm
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
  filter_upwards [hcl] with p hp
  have hp' : ∀ g, ‖K g p - K g p₀‖ ≤ ε / (μ.real 𝓕 + 1) := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    rw [hinv γ hγ, hinv γ hγ]
    exact (hp c hc).le
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const hfin fun g _ => hp' g) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cocompact_of_aniso (hP : GlobalTheory.Published.SiegelSetUnitary) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • J.map σ)) (han : ∀ x, form σ J x x = 0 → x = 0) :
    ∃ C : Set (UA σ J), IsCompact C ∧ ∀ h : UA σ J, ∃ γ ∈ ratU σ J, ∃ s ∈ C, h = γ * s := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ (c • J.map σ) (0 : Matrix (Fin n) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => han z (by
      have e : hE σ (c • J.map σ) z z = c * hE σ (J.map σ) z z := by
        simp only [hE, Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e] at hz
      rw [GlobalTheory.ThK.AnConv.form_eq hσ, (mul_eq_zero.1 hz).resolve_left hc, map_zero])⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient hP hcm hJ hW
  let e : UA σ J ≃* GAd σ (c • J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc)
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  refine ⟨e.symm '' C, hC.image he', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, hgs⟩ := hcov (e g)
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine ⟨e.symm γ, Subgroup.mem_subgroupOf.2 ⟨u, hu⟩, e.symm s, ⟨s, hs, rfl⟩, ?_⟩
  rw [← map_mul, ← hgs, MulEquiv.symm_apply_apply]

theorem hasSig_neg {n r : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r 0) : HasSig (-M) 0 r := by
  obtain ⟨hs, A, hA⟩ := h
  refine ⟨by omega, A.submatrix id Sum.swap, ?_⟩
  ext (i | i) (j | j)
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · have := congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at this
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.submatrix_apply, id, Sum.swap_inr, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul, this]

theorem aniso_skew {n r : ℕ} (B : Base F E) (hB : B.IsGood σ) (X : Spc F E n) (h : X.IsSkew σ B r 0) :
    ∀ x, form σ X.J x x = 0 → x = 0 := by
  intro x hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : E →+* ℂ := (B.emb w).1
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  have hy : (fun i => τ (x i)) ⬝ᵥ (X.J.map τ) *ᵥ star (fun i => τ (x i)) = 0 := by
    have := congrArg τ hx
    rw [map_zero] at this
    have hs : (star fun i => τ (x i)) = τ ∘ fun i => σ (x i) := by
      ext i; simp [hcm]
    rw [← this, hs, form, RingHom.map_dotProduct]
    show (τ ∘ x) ⬝ᵥ _ = (τ ∘ x) ⬝ᵥ _
    congr 1
    ext i
    exact (RingHom.map_mulVec τ X.J _ i).symm
  have hy' : (fun i => τ (x i)) ⬝ᵥ (-(Complex.I • X.J.map τ)) *ᵥ star (fun i => τ (x i)) = 0 := by
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_neg, dotProduct_smul, hy, smul_zero, neg_zero]
  have := GlobalTheory.ThK.AnConv.aniso_sig (hasSig_neg (h.sig w)) _ hy'
  funext i
  exact τ.injective (by simpa using congrFun this i)

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v h => h.1.trans h.2)

theorem continuous_liftW_small : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 →
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
      ∀ Φ₂ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Ψ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Continuous (GlobalTheory.ThK.DoublingLifts.liftW om' μ 𝓕 Φ₂ (G.M'.I om' Ψ')) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hp hq μ 𝓕 hμ h𝓕 Φ₂ hΦ₂ Ψ' hΨ'
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hb := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _
    (Check.isPair_of_isTriple hT).2).1
  obtain ⟨c₁, i₁, -⟩ := hb Ψ' (polData_le_schA B G.M' hT.geo.hM' (Submodule.mem_inf.1 hΨ').1)
  obtain ⟨c₂, i₂, -⟩ := hb Φ₂ (polData_le_schA B G.M' hT.geo.hM' (Submodule.mem_inf.1 hΦ₂).1)

  have hV' := hT.geo.hV'
  rw [hq] at hV'
  have hW := hT.geo.hW
  rw [hp, hq] at hW
  obtain ⟨C₁, hC₁, hcov₁⟩ := cocompact_of_aniso hKP.siegelSetUnitary hcm G.V'.J (one_ne_zero : (1 : E) ≠ 0)
    (by rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hV') (GlobalTheory.ThK.AnConv.aniso_herm B hT.base G.V' hV')
  obtain ⟨c, hc, hσc⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  obtain ⟨C₂, hC₂, hcov₂⟩ := cocompact_of_aniso hKP.siegelSetUnitary hcm G.W.J hc
    (GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hW c hc hσc) (aniso_skew B hT.base G.W hW)
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ a' G.V'.J
  obtain ⟨hTG', -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := hT.geo.hM'.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V'.J
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.W.J

  have hI : Continuous (G.M'.I om' Ψ') :=
    continuous_setIntegral_cocompact (ratU σ G.V'.J) G.M'.μ G.M'.dom C₁ hT.geo.hM'.dom hC₁ hcov₁
      (fun g h => theta om' Ψ' g h) c₁ fun γ hγ g h => by simpa using i₁ γ hγ 1 (one_mem _) g h
  have hIinv : ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Ψ' (γ * h) = G.M'.I om' Ψ' h := fun γ hγ h => by
    have e : ∀ g, theta om' Ψ' g (γ * h) = theta om' Ψ' g h := fun g => by
      simpa using i₁ 1 (one_mem _) γ hγ g h
    simp only [Model.I, e]
  exact continuous_setIntegral_cocompact (ratU σ G.W.J) μ 𝓕 C₂ h𝓕 hC₂ hcov₂
    (fun h g => G.M'.I om' Ψ' h * starRingEnd ℂ (theta om' Φ₂ g h))
    ((hI.comp continuous_fst).mul (Complex.continuous_conj.comp (c₂.comp (continuous_snd.prodMk continuous_fst))))
    fun γ hγ h g => by
      have e : theta om' Φ₂ g (γ * h) = theta om' Φ₂ g h := by simpa using i₂ 1 (one_mem _) γ hγ g h
      simp only [hIinv γ hγ h, e]

end GlobalTheory.ThK.LiftContDef

end
