import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTransSq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uj_smul_eq {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (s : A →+* A) (K : Matrix ι ι A) {c : A}
    (hc : IsUnit c) : Formalism.UG.UJ s (c • K) = Formalism.UG.UJ s K := by
  ext g
  show Formalism.UG.cT s (g : Matrix ι ι A) * (c • K) * (g : Matrix ι ι A) = c • K ↔
    Formalism.UG.cT s (g : Matrix ι ι A) * K * (g : Matrix ι ι A) = K
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hc.smul_left_cancel

theorem isMulRightInvariant_skew (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  obtain ⟨d, hd'⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  set δ : E := σ d - d with hδdef
  have hδ : δ ≠ 0 := sub_ne_zero.2 hd'
  have hσδ : σ δ = -δ := by rw [hδdef, map_sub, hss]; abel
  set J' : Matrix (Fin n) (Fin n) E := δ • Jᵀ with hJ'
  have hH : IsHermND σ J' := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [hJ', Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hJ]
      ring
    · rw [hJ', Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hδ) hd
  have hunit : IsUnit (inclR (F := F) (AF F) δ) := (Ne.isUnit hδ).map _
  have hJR : JR (F := F) (AF F) J' = (inclR (F := F) (AF F) δ) • JR (F := F) (AF F) Jᵀ := by
    ext i j; simp [JR, hJ']
  have hEq : HR (AF F) σ Jᵀ = HR (AF F) σ J' := by
    unfold HR; rw [hJR, uj_smul_eq _ _ hunit]
  let e2 : HA (AF F) σ Jᵀ ≃ₜ* HA (AF F) σ J' :=
    { toMulEquiv := MulEquiv.subgroupCongr hEq
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))
  haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ J') := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J'))
  haveI : BorelSpace (HA (AF F) σ J') := ⟨rfl⟩
  let e := (GlobalTheory.ThetaRightTranslate.toHA σ J).trans e2
  refine GlobalTheory.ThetaRightTranslate.isMulRightInvariant_of_equiv e μ ?_
  haveI : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hss hδ hσδ hH (μ.map e)

theorem det_ne_zero_of_isSkew (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} (X : Spc F E n) {r s : ℕ}
    (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul] at h
  have h' := right_ne_zero_of_mul h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h'
  exact fun h0 => h' (by rw [h0, map_zero])

theorem memLp_translate : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, MeasureTheory.MemLp (fun x => G.M'.I om' Φ (x * h)) 2 (μ.restrict 𝓕) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ h
  have hT := hM.triple
  obtain ⟨hc, hinv⟩ := GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ hΦ
  have hsq := (GlobalTheory.T.square_integrability hK F E σ B a a' G X om om' hT μ 𝓕 hμ h𝓕).2 Φ hΦ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := hμ
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_skew σ hT.base.cm G.W.J hT.geo.hW.skew
    (det_ne_zero_of_isSkew σ B G.W hT.geo.hW) μ
  haveI := GlobalTheory.ThetaRightTranslate.countable_ratU σ G.W.J
  have hi := GlobalTheory.integrableOn_fundamentalDomain_mul_right h𝓕 h
    (fun x => ((‖G.M'.I om' Φ x‖ ^ 2 : ℝ) : ℂ)) (fun γ hγ x => by simp only [hinv γ hγ x]) (by exact hsq.ofReal)
  have hm : AEStronglyMeasurable (fun x => G.M'.I om' Φ (x * h)) (μ.restrict 𝓕) :=
    (hc.comp (continuous_mul_const h)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact hi.re.congr (ae_of_all _ fun x => RCLike.ofReal_re (K := ℂ) _)

end GlobalTheory.ThKTransSq
