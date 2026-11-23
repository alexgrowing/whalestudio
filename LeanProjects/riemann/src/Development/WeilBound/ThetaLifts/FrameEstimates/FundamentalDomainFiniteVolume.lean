import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fv_exists_skew (hσ : IsCMExt F E σ) : ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  obtain ⟨-, hE, -, hc⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hss : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hc, hc, star_star])
  by_contra hn
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have hx : x - σ x = 0 := by
    by_contra h
    exact hn ⟨_, h, by rw [map_sub, hss, neg_sub]⟩
  have h2 := hc τ x
  rw [← sub_eq_zero.1 hx] at h2
  exact h2.symm

theorem fv_exists_herm (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ c : E, c ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (c • J)ᵀ := by
  have hd : ∀ c : E, c ≠ 0 → ((c • J)ᵀ).det ≠ 0 := fun c hc => by
    rw [Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hJ.2
  rcases hJ.1 with h | h
  · exact ⟨1, one_ne_zero, fun i j => by simpa using h j i, hd 1 one_ne_zero⟩
  · obtain ⟨c, hc, hs⟩ := fv_exists_skew hσ
    refine ⟨c, hc, fun i j => ?_, hd c hc⟩
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs, h j i]
    ring

omit [NumberField E] in
theorem fv_HR_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UG (cA σ) (incM F J) = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (c • J)ᵀ := by
  have hu : IsUnit (inclR (F := F) (AF F) c) := (IsUnit.mk0 c hc).map _
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ = (inclR (F := F) (AF F) c • incM F J)ᵀ := by
    ext i j
    exact map_mul (inclR (F := F) (AF F)) c (J j i)
  ext g
  show g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J ↔
    (g.1.map (cA σ))ᵀ * HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ * g.1 = HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ
  rw [hJ]
  have e : (g.1.map (cA σ))ᵀ * (inclR (F := F) (AF F) c • incM F J)ᵀ * g.1 =
      (inclR (F := F) (AF F) c • (g.1ᵀ * incM F J * g.1.map (cA σ)))ᵀ := by
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]
  rw [e, Matrix.transpose_inj, hu.smul_left_cancel]

omit [NumberField E] in
theorem fv_rat_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf (HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) =
      HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
  ext g
  rw [HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have h : ((γ.1.map (inclR (F := F) (AF F))).map (sigR (AF F) σ))ᵀ * J.map (inclR (F := F) (AF F)) *
        γ.1.map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F)) := by
      have h0 := g.2
      rw [← hγ] at h0
      exact h0
    show (γ.1.map (σ : E →+* E))ᵀ * J * γ.1 = J
    refine Matrix.map_injective hinj ?_
    show ((γ.1.map (σ : E →+* E))ᵀ * J * γ.1).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F))
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩

theorem fundamental_domain_finite_volume (hσ : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (S : Subgroup (GL (Fin n) (AE F E))) (hS : S = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) :
    letI : MeasurableSpace S := borel S
    ∀ (μ : Measure S) (D : Set S), μ.IsHaarMeasure →
      IsFundamentalDomain ((Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf S) D μ →
        μ D < ⊤ := by
  subst hS
  rw [fv_rat_eq]
  intro μ D hμ hD
  exact ((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hσ n J hJ).2 μ hμ).2 D hD

theorem finVolU : FinVolU := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  obtain ⟨c, hc, h⟩ := fv_exists_herm hσ hJ
  exact fundamental_domain_finite_volume hσ _ h _ (fv_HR_eq J hc)

end PositivityTheory.ThKEst

end
