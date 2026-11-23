import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelicStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalisedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProductsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrixStatement

noncomputable section

section Body
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem coefS_pure (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S →
      ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ →
      ∀ A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E),
        (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) →
        coefSN σ b J ψ dx db (pureN φ A) T S =
          (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
            ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  classical
  obtain ⟨hEu, hlat⟩ := GlobalTheory.T.adelic_measure_euler_product_decomposition F E σ hCM M J hJ n h2n ψ hψ dx hdx d b laminf lam hinf hlam
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b dx 1 _ _ hEu
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.hermitian_measure_euler_product F E σ hCM M J hJ n h2n ψ hψ db hdb d b laminf lam hinf hlam
  have hq := GlobalTheory.T.gram_matrix_integral_almost_all_places F E σ hCM M J hJ n h2n d b T hT
  have hqf := Filter.eventually_cofinite.1 hq
  refine ⟨S₀ ∪ S₁ ∪ hqf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  obtain ⟨ρ, U, hρ, hρs, hU, hUs, hI, hc, hbd, hlim⟩ := hS₁ S hS1
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S φ A hφ hA hAl
  have hΦdx : Integrable (pureN φ A) dx := GlobalTheory.T.schwartz_bruhat_integrable_adelic F E σ hCM M J hJ n h2n ψ hψ dx hdx _ hΦSB
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI
  have hInf := GlobalTheory.T.archimedean_gram_fibre_measure_exists F E σ hCM M J hJ n h2n d b laminf hinf minf hminf cI (hu _) φ hφ ρ hρ hρs
  have hV := fun v => GlobalTheory.T.local_gram_fibre_measure_unramified F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2 (fun k => U k v)
    (fun k => ⟨(hU k v).1, (hU k v).2.1, (hU k v).2.2.1⟩) (hUs v)
  have hUpos : ∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal :=
    fun k v => (hU k v).2.2.2
  have hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) := fun k => (hρ k).2.2.2
  have hck : ∀ k, (∫ y, testH σ b (ρ k) S (U k) y ∂db) ≠ 0 := by
    intro k
    rw [hc k]
    refine mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    exact_mod_cast (hUpos k v).ne'
  have a1 : ∀ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R'),
      hermMap f σ (hermOf R σ T hT) = hermOf R' σ T hT := fun f => hermMap_hermOf f σ T hT
  have h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      hermV σ v (hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x)) =
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) (projV v (projFin x)) := by
    intro x v
    simp only [hermV, hermFin, hermMap_sub, a1, hermMap_gramH]
    rfl
  have h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
      hermInf σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) = cI - gramH hCM hJ (Ainf F) (projInf x) := by
    intro x
    simp only [hermInf, hermMap_sub, a1, hermMap_gramH]
    rfl
  have key : ∀ k, ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
      ((∫ X, φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) /
          ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) *
        ∏ v ∈ S, (((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal /
            (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℝ) : ℂ) := by
    intro k
    have hf := GlobalTheory.T.siegel_weil_integral_normalised F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦdx
      (testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
      if v ∈ S then A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} else A v
    have hA'S : ∀ v ∈ S, A' v = A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} :=
      fun v hv => if_pos hv
    have hA'n : ∀ v, v ∉ S → A' v = latV b v := fun v hv => (if_neg hv).trans (hAl v hv)
    have hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        (projFin x ∈ boxFN A ∧ hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∈ boxH σ b n S (U k)) ↔
          projFin x ∈ boxFN A' := by
      intro x
      constructor
      · rintro ⟨h, h'⟩ v
        by_cases hv : v ∈ S
        · rw [hA'S v hv]
          refine ⟨h v, ?_⟩
          show _ ∈ U k v
          rw [← h3 x v]
          exact h'.1 v hv
        · rw [show A' v = A v from if_neg hv]
          exact h v
      · intro h
        refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hv : v ∈ S
          · have := h v
            rw [hA'S v hv] at this
            exact this.1
          · have := h v
            rwa [show A' v = A v from if_neg hv] at this
        · have := h v
          rw [hA'S v hv] at this
          rw [h3 x v]
          exact this.2
        · have := h v
          rw [hA'n v hv] at this
          rw [h3 x v]
          exact hS2 v hv _ this
    have hpt : ∀ x, pureN φ A x * testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) =
        pureN (fun X => φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ)) A' x := by
      intro x
      unfold pureN testH
      rw [h0 x]
      by_cases h : projFin x ∈ boxFN A'
      · obtain ⟨ha, hb⟩ := (hmem x).2 h
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]
        ring
      · rw [Set.indicator_of_notMem h, mul_zero]
        by_cases ha : projFin x ∈ boxFN A
        · have hb : hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∉ boxH σ b n S (U k) :=
            fun hb => h ((hmem x).1 ⟨ha, hb⟩)
          rw [Set.indicator_of_notMem hb]
          simp
        · rw [Set.indicator_of_notMem ha]
          simp
    have hmeasA' : ∀ v, MeasurableSet (A' v) := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).1
      · rw [show A' v = A v from if_neg hv]
        exact (GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v) _ (hu _) (A v) (hA v).1 (hA v).2).1
    have hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤ := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).2
      · rw [hA'n v hv, hlat v]; exact ENNReal.one_ne_top
    have he := (hS₀ S hS0 _ (hInf.1 k).1 (hInf.1 k).2 A' hmeasA' hfinA' hA'n).2
    have htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1 := by
      simp [hlat]
    rw [htail] at he
    have hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) =
        ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal : ℂ) :=
      Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]
    have e1 : ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
        (∫ bb, fouH σ ψ db (testH σ b (ρ k) S (U k)) bb *
          (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) /
          ∫ y, testH σ b (ρ k) S (U k) y ∂db := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)
    rw [e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]
    rw [div_mul_div_comm]
  have lim1 : Filter.Tendsto (fun k => ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb /
        ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) Filter.atTop
      (nhds (coefSN σ b J ψ dx db (pureN φ A) T S)) := by
    have hχ : Continuous (chiT σ ψ T) := GlobalTheory.T.continuous_fourier_character_of_matrix F E σ hCM M J hJ n h2n ψ hψ T
    refine tendsto_integral_of_dominated_convergence (fun bb => ‖starN σ J ψ dx (pureN φ A) bb‖) ?_ hstar.norm ?_ ?_
    · intro k
      exact ((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    · intro k
      refine Filter.Eventually.of_forall fun bb => ?_
      rw [norm_mul, norm_mul, show ‖chiT σ ψ T bb‖ = 1 from hψ.2.1 _, mul_one, norm_div]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k bb))
    · refine Filter.Eventually.of_forall fun bb => ?_
      exact (hlim bb).mul_const _
  have lim2 := hInf.2.mul (tendsto_finset_prod S fun v _ =>
    (Complex.continuous_ofReal.tendsto _).comp (hV v).2)
  exact tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)

theorem pure_identity (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0)
    (hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : IsSchwartzArch φ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b _ 1 _ _ hEu
  obtain ⟨S₂, hS₂⟩ := coefS_pure σ hCM J hJ h2n ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT hdet
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula F E σ hCM M J hJ n h2n d b laminf hinf minf hminf _ (hu _) φ hφ
  have hφi' := hφi.self_of_nhds
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hlimC := GlobalTheory.T.siegel_eisenstein_unfolding_identity F E σ hCM M J hJ n h2n ψ hψ dx db _ hstar d b T
  have hsum := hEu.2.1
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hsum
  have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2
  refine ⟨?_, ?_⟩
  · have hs : S₁ ⊆ S₀ ∪ S₁ := Finset.subset_union_right
    exact (hS₁ (S₀ ∪ S₁) hs φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2)
      (fun v hv => hAl v fun h => hv (Finset.mem_union_left _ h))).1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  have hlim2 : Filter.Tendsto (fun S => coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    have hAS : ∀ v, v ∉ S → A v = latV b v := fun v hv => hAl v fun h => hv (hs0 h)
    rw [hS₂ S hs2 φ hφ A hA hAS, (hS₁ S hs1 φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2) hAS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

end Pure

end GlobalTheory.CompanionTheory.SiegelND.Coef

end Body

section Final

open GlobalTheory.CompanionTheory.SiegelND.Coef

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
    μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ T : Matrix (Fin n) (Fin n) E, (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n h2n ψ hψ dx hdx db hdb μ 𝓕 hμ h𝓕 Φ hΦ T hT hdet
  classical
  let b := Module.finBasis F E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1) b laminf hinf.1 n
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1 n
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) 1
      (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero F E σ hCM n M J hJ (by omega) T hT hdet _ b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products F E σ hCM M J hJ n h2n _ b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Coef.pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, Coef.pureN (φ i) (A i) X := funext hsum
  have hP := fun i => Coef.pure_identity σ hCM J hJ h2n ψ hψ dx hdx db hdb _ _ b laminf lam hinf hlam minf hminf m hm
    T hT hdet hEu S (φ i) (hφ i) (A i) (hA i) (hAl i)
  have e1 : ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) =
      ∑ i, ∫ X, Coef.pureN (φ i) (A i) X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
    simp only [hsum]
    exact integral_finset_sum _ fun i _ => (hP i).1
  rw [e1, hΦe, GlobalTheory.T.siegel_weil_hermitian_coefficient F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb T N _ hSB]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end Final
