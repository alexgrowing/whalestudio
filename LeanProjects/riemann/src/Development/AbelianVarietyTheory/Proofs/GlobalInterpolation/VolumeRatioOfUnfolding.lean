import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLattStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrderStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddCharStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpowStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdeleCoordinatesCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualSumPairingMapEqPiStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreMeasureFamilyMapHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOrthogonalComplementUnitaryFrameOfMatrixStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitarySignatureStabiliserCosetCutoffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlacesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreLintegralNeZeroOfPosStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.VolRatioUnfold

section Arch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hR_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (y i)) = inclR R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, JR, sigR, inclR, map_sum, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sum]

theorem exists_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {x : V}
    (hx : x ≠ 0) : ∃ φ : V → ℝ, (Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ {y | y ≠ 0} ∧ ∀ y, 0 ≤ φ y) ∧
      0 < φ x := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := 0) (s := {y : V | y ≠ 0})
    (isOpen_ne.mem_nhds hx)
  exact ⟨f, ⟨h3.continuous, h2, h1, fun y => (h4 ⟨y, rfl⟩).1⟩, by rw [h5]; exact one_pos⟩

theorem arch (hR3 : ActionCoordinates.RealPlaceMeasures) (c : CDHaar) (hσ : IsCMExt F E σ) {T : Type} [Fintype T]
    {τ : T → (E →+* ℂ)} {θ : T → (Ainf F ⊗[F] E →+* ℂ)}
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ))
    {M P Q P' Q' : ℕ} (hM : P + Q = M) (hM' : P' + Q' + 1 = P + Q) {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ}
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) (x : Fin M → E) (β : F) (hβ : β = 1 ∨ β = -1)
    (hx : hE σ J x x = algebraMap F E β) (ψ : AddChar (AF F) ℂ) (hψ : ∀ a, psiInf F ψ a = LocalAdditiveCharacterDual.stdInf F a) :
    ∃ (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (a : ℝ≥0∞), Measurable Φi ∧ a ≠ 0 ∧ a ≠ ⊤ ∧
      (∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
          (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)),
        SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
        SelfDual νi (fun s t => psiInf F ψ (s * t)) →
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi →
        ∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β)) = a) ∧
      ∀ (C : T → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ)
        (j : (T → UpqT P' Q') →* (T → UpqT P Q)) (o : (T → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E))
        (ν : Measure (LatticeTensorUnfolding.RCosets j)),
        (∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
          ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A ρ *ᵥ fun i => τ ρ (x i)) = 0) →
        (∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
          UpqT.mat (j b ρ) *ᵥ (A ρ *ᵥ fun i => τ ρ (x i)) = A ρ *ᵥ fun i => τ ρ (x i)) →
        (∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x i))) →
        LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν →
        ∫⁻ s : LatticeTensorUnfolding.RCosets j, Φi (o s.out) ∂ν = (ActionCoordinates.cM M)⁻¹ ^ Fintype.card T * a := by
  classical
  obtain ⟨hSD, -, hQ⟩ := hR3
  obtain ⟨r, hr1, hr2, hrθ, hrs, hrn⟩ := GlobalTheory.T.exists_realAdele_coordinates_cmType F E σ hσ T τ θ hτ hθ
  obtain ⟨e, he, heh⟩ := GlobalTheory.T.exists_realAdelicHermitian_signature_coordinates F E σ hσ T τ θ hτ hθ M P Q hM J hJ A hA
  haveI : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := (GlobalTheory.ArchUnitaryTop.top_facts F E σ M 1 J).2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨fib, hfib⟩ := GlobalTheory.RealPlaceCompare.exists_isDxDq P Q

  obtain ⟨b, hb1, hb⟩ : ∃ b : ℝ, (b = 1 ∨ b = -1) ∧ r (algebraMap F (Ainf F) β) = fun _ => b := by
    rcases hβ with rfl | rfl
    · exact ⟨1, Or.inl rfl, by rw [map_one, map_one]; rfl⟩
    · exact ⟨-1, Or.inr rfl, by rw [map_neg, map_one, map_neg, map_one]; rfl⟩
  have hb0 : b ≠ 0 := by rcases hb1 with rfl | rfl <;> norm_num
  have htr : ∀ z ρ, r (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) ρ = 2 * (θ ρ z).re := by
    intro z ρ
    have h := hrθ (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) ρ
    have h0 : Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z ⊗ₜ[F] (1 : E) = z + sigR (Ainf F) σ z :=
      GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ z
    rw [h0, map_add, GlobalTheory.Mem.VolExists.infEmb_sigR hσ (hθ ρ), Complex.add_conj] at h
    exact_mod_cast h
  have hhalf : ∀ ρ, r (algebraMap F (Ainf F) (1 / 2)) ρ = 1 / 2 := by
    intro ρ
    have h2 : algebraMap F (Ainf F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Ainf F)) 2, ← map_mul]; norm_num
    have h3 := congrFun (congrArg r h2) ρ
    rw [map_mul, map_one, map_ofNat] at h3
    simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.one_apply] at h3
    linarith
  have hq : ∀ X ρ, ActionCoordinates.qf (e X ρ) = r (qR (Ainf F) σ J (X 0)) ρ := by
    intro X ρ
    rw [qR, map_mul, Pi.mul_apply, hhalf, htr, heh, ActionCoordinates.qf]; ring
  set xr : T → ActionCoordinates.Wsp P Q := fun ρ => A ρ *ᵥ fun i => τ ρ (x i) with hxr
  have hxe : ∀ ρ, e (ratTup (Ainf F) fun _ => x) ρ = xr ρ := by
    intro ρ
    rw [he]
    congr 1
    funext i
    exact (hθ ρ).1 (x i)
  have hxq : ∀ ρ, ActionCoordinates.qf (xr ρ) = b := by
    intro ρ
    have h1 := heh (ratTup (Ainf F) fun _ => x) (ratTup (Ainf F) fun _ => x) ρ
    rw [hxe, ActionCoordinates.herm_self] at h1
    have h2 : hR (Ainf F) σ J (ratTup (F := F) (Ainf F) (fun _ : Fin 1 => x) 0) (ratTup (F := F) (Ainf F) (fun _ : Fin 1 => x) 0) =
        algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) := by
      refine (hR_ratTup (Ainf F) J x x).trans ?_
      rw [hx, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rfl
    rw [h2, ← hrθ, hb] at h1
    exact_mod_cast h1.symm
  have hx0 : ∀ ρ, xr ρ ≠ 0 := by
    intro ρ h
    have := hxq ρ
    rw [h, GlobalTheory.RealPlaceCompare.qf_eq, GlobalTheory.RealPlaceCompare.qf_zero] at this
    exact hb0 this.symm
  choose φ hφ hφx using fun ρ => exists_bump (hx0 ρ)
  have hφm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    (hφ ρ).1.measurable.ennreal_ofReal
  have hΦm : Measurable fun z : T → ActionCoordinates.Wsp P Q => ∏ ρ, ENNReal.ofReal (φ ρ (z ρ)) :=
    Finset.measurable_prod _ fun ρ _ => (hφm ρ).comp (measurable_pi_apply ρ)
  have hem : Measurable e := e.continuous.measurable
  have hfb := GlobalTheory.RealPlaceCompare.isDxDq_local hfib b
  refine ⟨fun X => ∏ ρ, ENNReal.ofReal (φ ρ (e X ρ)), ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib b),
    hΦm.comp hem, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun ρ _ =>
      GlobalTheory.T.hermitianNormFibre_lintegral_ne_zero_of_pos hQ c P Q b hb1 (xr ρ) (hxq ρ) fib hfb (φ ρ) (hφ ρ).1 (hφx ρ)
  · refine ENNReal.prod_ne_top fun ρ _ => ?_
    have hi := (hfib.2.2 (φ ρ) (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 b (Set.mem_univ _)
    exact hi.lintegral_lt_top.ne
  · intro μi νi fi hμ hν hfi
    have hdx : (ActionCoordinates.dx P Q).IsAddHaarMeasure := GlobalTheory.RealPlaceCompare.isAddHaar_dx P Q
    have h1 : μi.map e = Measure.pi fun _ : T => ActionCoordinates.dx P Q := by
      refine GlobalTheory.T.selfDual_sumPairing_map_eq_pi T _ _ e (-1) ActionCoordinates.bil _ hdx
        (((hSD (-1) (Or.inr rfl)).1 P Q _ hdx).2 rfl) μi _ (fun X Y => ?_) hμ
      rw [hψ, hrs]
      congr 4
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [BR, Fin.sum_univ_one, htr, heh, GlobalTheory.RealPlaceCompare.bil_eq, GlobalTheory.RealPlaceCompare.herm_eq,
        ← GlobalTheory.RealPlaceCompare.herm_star (e X ρ)]
      simp
    let r' : Ainf F ≃ₜ+ (T → ℝ) := { r.toAddEquiv with continuous_toFun := hr1, continuous_invFun := hr2 }
    have h2 : νi.map r' = volume := by
      refine GlobalTheory.T.selfDual_sumPairing_map_eq_pi T _ _ r' (-1) (fun t s : ℝ => t * s) volume inferInstance
        (((hSD (-1) (Or.inr rfl)).2 _ inferInstance).2 rfl) νi _ (fun s t => ?_) hν
      rw [hψ, hrs, map_mul]
      rfl
    have h3 := GlobalTheory.T.isFibreMeasureFamily_map_homeomorph _ _ _ _ e.toHomeomorph r'.toHomeomorph μi νi _
      (fun (z : T → ActionCoordinates.Wsp P Q) ρ => ActionCoordinates.qf (z ρ)) _ fi (fun X => funext fun ρ => hq X ρ) hfi
    have h1' : μi.map e.toHomeomorph = Measure.pi fun _ : T => ActionCoordinates.dx P Q := h1
    have h2' : νi.map r'.toHomeomorph = volume := h2
    rw [h1', h2'] at h3
    have hB : r'.toHomeomorph '' {c | ∀ w, c w ≠ 0} = {t | ∀ ρ, t ρ ≠ 0} := by
      ext t
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hrn a).1 ha
      · intro ht
        refine ⟨r.symm t, (hrn _).2 ?_, r.apply_symm_apply t⟩
        rw [r.apply_symm_apply]; exact ht
    rw [hB] at h3
    have hBo : IsOpen {t : T → ℝ | ∀ ρ, t ρ ≠ 0} := by
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun ρ => isOpen_ne.preimage (continuous_apply ρ)
    have hfib' : IsFibreFamily (ActionCoordinates.dx P Q) ActionCoordinates.qf id {x | x ≠ 0} (volume : Measure ℝ) Set.univ fib := by
      rw [GlobalTheory.RealPlaceCompare.qf_eq]; exact hfib
    have h4 := GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral T _ (ActionCoordinates.dx P Q) ActionCoordinates.qf
      (by rw [GlobalTheory.RealPlaceCompare.qf_eq]; exact GlobalTheory.RealPlaceCompare.continuous_qf) _ isOpen_ne fib hfib' _ hBo _ h3
      (fun _ => b) (fun _ => hb0) φ hφ
    have h5 : r'.toHomeomorph.symm (fun _ => b) = algebraMap F (Ainf F) β := by
      rw [← hb]; exact r.symm_apply_apply _
    rw [h5] at h4
    exact (lintegral_map hΦm hem).symm.trans h4
  · intro C j o ν hC hj ho hν
    have hne : ∀ ρ, star (xr ρ) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ xr ρ ≠ 0 := by
      intro ρ
      rw [GlobalTheory.QuadricSection.form_self, ← GlobalTheory.RealPlaceCompare.qf_eq, hxq]
      exact_mod_cast hb0
    let ι : T → UpqT P' Q' → UpqT P Q := fun ρ h => j (Pi.mulSingle ρ h) ρ
    have hι : ∀ ρ h, UpqT.mat (ι ρ h) * C ρ = C ρ * UpqT.mat h ∧ UpqT.mat (ι ρ h) *ᵥ xr ρ = xr ρ := by
      intro ρ h
      have := hj (Pi.mulSingle ρ h) ρ
      rwa [Pi.mulSingle_eq_same] at this
    have hjι : ∀ g ρ, j g ρ = ι ρ (g ρ) := fun g ρ =>
      GlobalTheory.UnfoldingCompare.eq_of_frame hM' (hne ρ) (hC ρ).1 (hC ρ).2
        ((hj g ρ).1.trans (hι ρ _).1.symm) ((hj g ρ).2.trans (hι ρ _).2.symm)
    have hfr : ∀ ρ, ActionCoordinates.IsPerpFrame (xr ρ) (Matrix.toLin' (C ρ)) (ι ρ) := fun ρ =>
      GlobalTheory.T.isOrthogonalComplementUnitaryFrame_of_matrix P Q P' Q' hM' (xr ρ) (by rw [hxq]; exact hb0) (C ρ) (hC ρ).1 (hC ρ).2 (ι ρ) (hι ρ)
    choose u hu using fun ρ => GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff c P Q P' Q' (xr ρ) (by rw [hxq]; exact hb0) _ (ι ρ) (hfr ρ)
      ((hQ P Q b hb1 (xr ρ) (hxq ρ)).2.2 P' Q' _ _ (hfr ρ)).1
    have h := GlobalTheory.T.unitaryQuotientIntegral_prod_over_places hQ c T P Q P' Q' b hb1 xr hxq _ ι hfr u hu j hjι ν hν fib hfb _ hφm
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hM] at h
    rw [← h]
    refine lintegral_congr fun s => Finset.prod_congr rfl fun ρ _ => ?_
    rw [he, ho]
    rfl

end Arch

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem local_value (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hσ : IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (v : HeightOneSpectrum (𝓞 F))
    (hv : SelfDualUnramifiedPlaces.UnramifiedPlace F E v) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (hi : LocalAdditiveCharacterDual.IndexFinite F ψ v)
    (L : Submodule (SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) (hL : SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L)
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
    (hμ : SelfDual μ fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (hν : SelfDual ν fun s t => psiV F ψ v (s * t))
    (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hfib : IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib)
    (β : Fv F v) (hβ : Valued.v β = 1) :
    fib β {X | X 0 ∈ L} = ENNReal.ofReal (LocalAdditiveCharacterDual.locDens F E ψ M v) := by
  obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.exists_localComponent_adelicAddChar F ψ hψ v hi
  have hχ' : (χ : Fv F v → ℂ) = psiV F ψ v := funext hχψ
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta := (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  obtain ⟨⟨c, hc⟩, h⟩ := hL5 F E σ hσ M J hM hJ v η hEta χ hχ
  have h1 := ((h c hc L ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ
    (by rw [SdW, hχ']; exact hμ) ν (by rw [SdR, hχ']; exact hν)).2.2 β hβ).1 Set.univ {c | c ≠ 0} fib
    (Set.subset_univ _) subset_rfl hfib
  refine h1.1.trans (congrArg _ ?_)
  have h2 := GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow F ψ v c (by simpa only [PlaceSplittingTypes.IsDualExp, hχψ] using hc)
  rw [LocalAdditiveCharacterDual.locDens, h2, PlaceSplittingTypes.densityValue, PlaceSplittingTypes.dualIndex, LocalAdditiveCharacterDual.eulerInv, hη]
  rfl

theorem tprod_ofReal {ι : Type} {f : ι → ℝ} (h0 : ∀ i, 0 ≤ f i) (hf : Multipliable f) :
    ∏' i, ENNReal.ofReal (f i) = ENNReal.ofReal (∏' i, f i) := by
  refine HasProd.tprod_eq ?_
  have h := (ENNReal.continuous_ofReal.tendsto _).comp hf.hasProd
  refine h.congr fun s => ?_
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i

end Fin

theorem ratio_of_eq {V V' c p : ℝ} (hV : 0 < V) (hV' : 0 < V') (hc : 0 < c) (hp : 0 < p) {f : ℕ} {a : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (h : (ENNReal.ofReal V)⁻¹ * (ENNReal.ofReal V' * ((ENNReal.ofReal c)⁻¹ ^ f * a)) = a * ENNReal.ofReal p) :
    V' / V = c ^ f * p := by
  have h1 := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hV.le,
    ENNReal.toReal_ofReal hV'.le, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal hp.le] at h1
  have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha ha'
  have hcf : 0 < c ^ f := pow_pos hc f
  rw [inv_pow] at h1
  field_simp at h1 ⊢
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hE_coords (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (fun i => W.frame.repr x i) (fun i => W.frame.repr y i) = W.hT x y := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]; rfl

theorem tsum_coords (D : D7) (W : HSpace D.host.E) (s : Bool) (β : D.host.F)
    (hβE : algebraMap D.host.F D.host.E β = if s then 1 else -1) (G : (Fin 1 → Fin W.rank → D.host.E) → ℝ≥0∞) :
    ∑' y : {y : Fin 1 → Fin W.rank → D.host.E | y 0 ≠ 0 ∧
        hE D.sp.cm.sig W.gram (y 0) (y 0) = algebraMap D.host.F D.host.E β}, G y =
      ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)}, G (LatticeTensorUnfolding.coords W x'.1) := by
  let eq : {x' : W.V // W.hT x' x' = (if s then 1 else -1)} ≃
      {y : Fin 1 → Fin W.rank → D.host.E | y 0 ≠ 0 ∧
        hE D.sp.cm.sig W.gram (y 0) (y 0) = algebraMap D.host.F D.host.E β} :=
    Equiv.subtypeEquiv (W.frame.equivFun.toEquiv.trans (Equiv.funUnique (Fin 1) _).symm) fun y => by
      have e1 : hE D.sp.cm.sig W.gram (W.frame.equivFun y) (W.frame.equivFun y) = W.hT y y := hE_coords D W y y
      change _ ↔ W.frame.equivFun y ≠ 0 ∧ hE D.sp.cm.sig W.gram (W.frame.equivFun y) (W.frame.equivFun y) = _
      rw [e1, hβE]
      refine ⟨fun h => ⟨fun h0 => ?_, h⟩, fun h => h.2⟩
      rw [LinearEquiv.map_eq_zero_iff] at h0
      rw [h0] at h
      cases s <;> simp at h
  rw [← eq.tsum_eq]; rfl

set_option maxHeartbeats 1000000 in

theorem ratio_of_setting (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hR3 : ActionCoordinates.RealPlaceMeasures)
    (hEu : LocalAdditiveCharacterDual.EulerProductOfDensities)
    (hSW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J)
    (D : D7) (hU : LatticeTensorUnfolding.Unfolding D) (hV : VolTie D) (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool)
    (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V) (hS : LatticeTensorUnfolding.HidaSetting W W' P Q P' Q' s x ι)
    (hL : ∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) :
    D.vol W' / D.vol W =
      ((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
        ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank := by
  classical
  have hun := hU W W' P Q P' Q' s x ι hS hL
  obtain ⟨hW, hsig, hr, hstep, hx, -, -, -, hW', hsig'⟩ := hS
  have hσ := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hM : P + Q = W.rank := by simpa [hsig τ₀] using sig_sum W hW τ₀
  have hM' : P' + Q' + 1 = P + Q := by cases s <;> simp at hstep <;> omega
  obtain ⟨⟨μ, hμ⟩, h1⟩ := hV W P Q hW hsig
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := h1 μ hμ
  have hvol := h2 𝓕 h𝓕
  obtain ⟨⟨μ', hμ'⟩, h1'⟩ := hV W' P' Q' hW' hsig'
  obtain ⟨⟨𝓕', h𝓕'⟩, h2'⟩ := h1' μ' hμ'
  have hvol' := h2' 𝓕' h𝓕'
  obtain ⟨⟨θ, hθ⟩, h3⟩ := hμ.2
  obtain ⟨A, hA⟩ := (h3 θ hθ).1
  obtain ⟨⟨⟨ψ, hψ, hψi⟩, -⟩, -, -, hEP⟩ := hEu D.host.F D.host.E D.sp.cm.sig hσ D.sp.cm.cmUnram
  obtain ⟨hfin, hpos, -, hmul, hppos, hval⟩ := ((hEP W.rank (by omega)).2 ψ hψ).2 1 (fun a => by simp [hψi])
  set β : D.host.F := if s then 1 else -1 with hβ
  have hβ1 : β = 1 ∨ β = -1 := by cases s <;> simp [hβ]
  have hβE : algebraMap D.host.F D.host.E β = if s then 1 else -1 := by cases s <;> simp [hβ]
  have hβ0 : β ≠ 0 := by rcases hβ1 with h | h <;> simp [h]
  obtain ⟨Φi, a, hΦi, ha0, hat, hfibre, hquot⟩ := arch hR3 D.cd hσ (GlobalTheory.VolRatioCheck.place_bijective D) hθ hM hM' hJ hA
    (fun i => W.frame.repr x i) β hβ1 (by rw [hE_coords, hx, hβE]) ψ hψi
  obtain ⟨I, hI, hunf⟩ := hun μ μ' hμ hμ' 𝓕 𝓕' h𝓕 h𝓕' (by rw [hvol]; exact ENNReal.ofReal_lt_top)
    (by rw [hvol']; exact ENNReal.ofReal_lt_top) Φi hΦi
  have hIa : I = (ActionCoordinates.cM W.rank)⁻¹ ^ Fintype.card D.what₂.Tau * a := by
    obtain ⟨⟨C, hC⟩, h4⟩ := (hI.2 θ hθ).2 A hA
    obtain ⟨⟨j, hj⟩, h5⟩ := h4 C hC
    obtain ⟨⟨o, ho⟩, h6⟩ := h5 j hj
    obtain ⟨⟨ν, hν⟩, h7⟩ := h6 o ho
    rw [← h7 ν hν]
    exact hquot C j o ν hC hj ho hν
  have hcard : Fintype.card D.what₂.Tau = D.R.f := by
    rw [Fintype.card_of_bijective (GlobalTheory.VolRatioCheck.place_bijective D)]; exact fDeg_host D

  have hlat := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat W
  have hsd := (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ.2 hlat).1
    (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm W)
  haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  let b := Module.finBasis D.host.F D.host.E
  let Φv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin 1 → Fin W.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ :=
    fun v => {X | X 0 ∈ GlobalTheory.AdelicU.latLoc D.host.F (GlobalTheory.AdelicU.frameLat W) v}.indicator 1
  let Φf : (Fin 1 → Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    {X | X 0 ∈ latHat D.host.F D.host.E (GlobalTheory.AdelicU.frameLat W : Set (Fin W.rank → D.host.E))}.indicator 1
  have hpure : IsPureFin b Φf Φv :=
    ⟨GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion _ _ _ _ hlat, (GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice _ _ _ _ b _ hlat).mono fun v hv => by simp only [Φv, hv],
      GlobalTheory.T.indicator_completedLattice_eq_finprod_local _ _ _ _ hlat⟩
  have hsw := hSW _ _ _ hσ _ _ hJ hr β hβ0 _ b (LatticeTensorUnfolding.latTensor (L0c D W) Φi) Φi Φf Φv hΦi hpure
    (fun v Y => by by_cases h : Y 0 ∈ GlobalTheory.AdelicU.latLoc D.host.F (GlobalTheory.AdelicU.frameLat W) v <;> simp [Φv, h])
    (fun X => by
      rw [LatticeTensorUnfolding.latTensor, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice, mul_comm]
      by_cases h : projFin X 0 ∈ latHat D.host.F D.host.E (GlobalTheory.AdelicU.frameLat W : Set (Fin W.rank → D.host.E)) <;>
        simp [Φf, h])
  obtain ⟨⟨μi, hμi⟩, ⟨νi, hνi⟩, ⟨μv, hμv⟩, ⟨νv, hνv⟩, h8⟩ := (((hsw.2 ψ hψ).2 μ hμ.1).2 𝓕 h𝓕)
  obtain ⟨⟨fi, hfi⟩, ⟨fv, hfv⟩, h9⟩ := h8 μi νi μv νv hμi hνi hμv hνv
  have hmean := (h9 fi fv hfi hfv).2
  have hloc : ∀ v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap D.host.F (Fv D.host.F v) β)) =
      ENNReal.ofReal (LocalAdditiveCharacterDual.locDens D.host.F D.host.E ψ W.rank v) := by
    intro v
    obtain ⟨Lv, hLv, hmem⟩ := GlobalTheory.T.exists_selfDualLattice_completion_maxOrder _ _ _ _ _ _ hJ hlat hsd v
    have hop := (GlobalTheory.LocalDensityCompare.lattice_compact_open v D.sp.cm.sig hσ Lv hLv.1 hLv.2.1).2
    have hlc := GlobalTheory.LocalDensityCompare.lcs (F := D.host.F) (E := D.host.E) v
    haveI := hlc.2.1
    haveI : BorelSpace (Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have hms : MeasurableSet {X : Fin 1 → Fin W.rank → Fv D.host.F v ⊗[D.host.F] D.host.E | X 0 ∈ Lv} :=
      hop.measurableSet
    rw [← local_value hL5 hσ (by omega) hJ v
      (fun w _ => GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm w) hψ (hfin v) Lv hLv _ _ (hμv v) (hνv v) _ (hfv v)
      (algebraMap D.host.F (Fv D.host.F v) β) (by rcases hβ1 with h | h <;> simp [h]),
      ← lintegral_indicator_one hms]
    refine lintegral_congr fun X => ?_
    by_cases h : X 0 ∈ Lv
    · have h' := (hmem _).1 h
      simp [Φv, h, h']
    · have h' := mt (hmem _).2 h
      simp [Φv, h, h']
  simp only [hloc] at hmean
  rw [tprod_ofReal (fun v => (hpos v).le) hmul, hfibre μi νi fi hμi hνi hfi, meanL] at hmean
  have hsum := (lintegral_congr fun h => tsum_coords D W s β hβE
    (LatticeTensorUnfolding.atInv D.sp.cm.sig W.gram (LatticeTensorUnfolding.latTensor (L0c D W) Φi) h)).trans hunf
  replace hmean := (congrArg ((μ 𝓕)⁻¹ * ·) hsum).symm.trans hmean
  simp only [hIa, hvol, hvol', hcard, ActionCoordinates.cM] at hmean
  have hc : 0 < (2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ) := by have := Real.pi_pos; positivity
  rw [ratio_of_eq (D.vol_pos W) (D.vol_pos W') hc hppos ha0 hat hmean, mul_div_assoc]
  congr 1
  simpa [LocalAdditiveCharacterDual.absInf, LocalAdditiveCharacterDual.dF, vInv_host, fDeg_host] using hval

theorem volumeRatio_of_unfolding (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hR3 : ActionCoordinates.RealPlaceMeasures)
    (hEu : LocalAdditiveCharacterDual.EulerProductOfDensities) (hInd : ∀ D, IsometryTransportFrames.VolIndep D) (hPerp : ∀ D, SelfDualLatticeComplements.UnitVectorPerp D)
    (hUnf : ∀ D, LatticeTensorUnfolding.Unfolding D)
    (hSW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J) :
    ∀ D : D7, VolTie D → VolumeRatio₂ D := by
  intro D hV W P Q hW hsig hr s hs
  obtain ⟨x, hx, L, W', ι, hL, hxL, ⟨hW', -, hsig'⟩, hiso, hrange, hlat, -⟩ :=
    hPerp D W W.rank P Q ⟨hW, rfl, hsig⟩ hr (if s then 1 else -1) (if s then P - 1 else P) (if s then Q else Q - 1)
      (by cases s <;> simp_all [SelfDualLatticeComplements.Step])
  refine ⟨x, hx, W', ι, hiso, hrange, hW', fun τ => by rw [hsig' τ]; cases s <;> rfl, ?_⟩
  let W₁ := IsometryTransportFrames.withLat W L hL.1 hL.2
  have hvol : D.vol W = D.vol W₁ :=
    (hInd D).2.2 hV W W₁ P Q ⟨hW, hsig⟩ ⟨hW, hsig⟩ (LinearEquiv.refl _ _) fun _ _ => rfl
  rw [hvol]
  refine ratio_of_setting hL5 hR3 hEu hSW D (hUnf D) hV W₁ W' P Q _ _ s x ι
    ⟨hW, hsig, hr, ?_, hx, hxL, hiso, hrange, hW', hsig'⟩ fun y => ?_
  · cases s <;> simp at hs ⊢ <;> omega
  · have hinj := SelfDualLatticeComplements.injective_of_isIsomEmb hiso
    constructor
    · intro hy
      have : ι y ∈ W'.L0.map (ι.restrictScalars (𝓞 D.host.E)) := ⟨y, hy, rfl⟩
      rw [hlat] at this
      exact this.1
    · intro hy
      have hp : ι y ∈ SelfDualLatticeComplements.perp W x := by rw [← hrange]; exact ⟨y, rfl⟩
      have : ι y ∈ W'.L0.map (ι.restrictScalars (𝓞 D.host.E)) := by rw [hlat]; exact ⟨hy, hp⟩
      obtain ⟨z, hz, e⟩ := this
      rwa [← hinj e]

end GlobalTheory.VolRatioUnfold
