import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCompactSetDensityBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzArchContinuousIntegrableStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenLE
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem isSplitK_of_isCoord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ)}
    {τ : NumberField.InfinitePlace F → (E →+* ℂ)} {Θ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)}
    (h : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.IsCoord σ e τ Θ) : IsSplitK e σ Θ := by
  refine ⟨h.1, h.2.1, fun a w => ?_⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hs : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) = algebraMap (Ainf F) (Ainf F ⊗[F] E) a := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have h1 := h.2.1 (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w
  rw [hs] at h1
  have h2 := h.2.2.2 (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w
  rw [← h1] at h2
  have h3 : Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) = 2 * a := by
    rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E))]
    simp [hCM.2.2.1, two_mul, two_nsmul]
  rw [h3, map_mul, map_ofNat] at h2
  have h4 : ((2 : NumberField.InfinitePlace F → ℝ) w) = 2 := rfl
  rw [Pi.mul_apply, h4] at h2
  push_cast at h2
  linear_combination (-1 / 2 : ℂ) * h2

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem denLE_image {V H : Type} [MeasurableSpace V] [MeasurableSpace H] {μ : Measure V} {ν : Measure H} {q : V → H}
    {T : V → V} {τ : H → H} (hT : MeasurableEmbedding T) (hτ : Measurable τ) (hq : ∀ X, q (T X) = τ (q X))
    {a c : ℝ≥0} (ha : a ≠ 0) (hμ : μ.map T = a • μ) (hν : ν.map τ = c • ν) {S : Set V} {C : ℝ≥0∞}
    (h : DenLE μ ν q S C) : DenLE μ ν q (T '' S) (((a⁻¹ * c : ℝ≥0) : ℝ≥0∞) * C) :=
  _root_.UpperTheory.Reformulated.B.Yhb9.main hT hτ hq ha hμ hν h

theorem dom_generic {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ} (hn : 0 < n) (hM : 2 * n < M)
    {H : Type} [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] {μ : Measure (Fin n → Fin M → K)}
    {ν : Measure H} {q : (Fin n → Fin M → K) → H} {C₀ : ℝ≥0∞} (hC : C₀ ≠ ⊤)
    (hbox : ∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) →
      DenLE μ ν q (boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n))))
    (hsh : ∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 →
      DenLE μ ν q S C → DenLE μ ν q (shearK a s '' S) C)
    (hq : Measurable q) (hbm : ∀ r : Fin n → W → ℝ, MeasurableSet (boxK (M := M) κ r))
    {φ : (Fin n → Fin M → K) → ℂ} {B : ℝ} (hB : ∀ X, ‖φ X‖ ≤ B)
    (hdec : ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R ε' : ℝ, 0 < ε' ∧ ∀ Y, MeasurableSet Y →
      ∫⁻ X in (goodK κ R ε')ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  have hε2 : ε / 2 ≠ 0 := by simp [ENNReal.div_eq_top, hε]
  obtain ⟨R, hR, htail⟩ := GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul K W κ n M H μ ν q C₀ hC hbox hq hbm φ hdec (ε / 2) hε2
  set Bc : ℝ≥0∞ := ENNReal.ofReal B with hBc
  have hBt : Bc + 1 ≠ ⊤ := by simp [hBc]
  have hδ : ε / 2 / (Bc + 1) ≠ 0 := by
    simp [ENNReal.div_eq_top, hε, hBc]
  obtain ⟨ε', hε', hbad⟩ := GlobalTheory.T.density_bound_from_box_volume_growth K W κ n M hn hM H μ ν q C₀ hC hbox hsh R hR _ hδ
  refine ⟨R, ε', hε', fun Y hY => ?_⟩
  have hsub : (goodK κ R ε')ᶜ ∩ q ⁻¹' Y ⊆ ((boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y) ∪
      ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y) := by
    rintro X ⟨hX, hXY⟩
    by_cases hb : X ∈ boxK κ (fun _ _ => R)
    · exact Or.inr ⟨⟨hb, hX⟩, hXY⟩
    · exact Or.inl ⟨hb, hXY⟩
  have h2 : ∫⁻ X in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε / 2 * ν Y := by
    calc ∫⁻ X in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in (boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y, Bc ∂μ :=
          lintegral_mono fun X => by
            rw [hBc, ← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hB X)
      _ = Bc * μ ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y) := by
          rw [setLIntegral_const]
      _ ≤ Bc * (ε / 2 / (Bc + 1) * ν Y) := by
          gcongr
          exact hbad Y hY
      _ ≤ (Bc + 1) * (ε / 2 / (Bc + 1)) * ν Y := by
          rw [← mul_assoc]
          gcongr
          exact le_self_add
      _ ≤ ε / 2 * ν Y := by
          gcongr
          exact ENNReal.mul_div_le
  calc ∫⁻ X in (goodK κ R ε')ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ((boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y) ∪
        ((boxK κ (fun _ _ => R) \ goodK κ R ε') ∩ q ⁻¹' Y), ‖φ X‖ₑ ∂μ := lintegral_mono_set hsub
    _ ≤ _ + _ := lintegral_union_le _ _ _
    _ ≤ ε / 2 * ν Y + ε / 2 * ν Y := add_le_add (htail Y hY) h2
    _ = ε * ν Y := by rw [← add_mul, ENNReal.add_halves]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem shearK_eq_rmul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n M : ℕ}
    (a : Fin n) (s : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    shearK a s X = GlobalTheory.CompanionTheory.SW.rmul R X (shearM a s) := by
  funext c i
  simp only [shearK, GlobalTheory.CompanionTheory.SW.rmul, shearM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : c = a
  · subst h
    simp [mul_comm]
  · simp [Function.update, h]

theorem shearK_neg {K : Type} [CommRing K] {n M : ℕ} (a : Fin n) (s : Fin n → K) (hs : s a = 0)
    (X : Fin n → Fin M → K) : shearK a (-s) (shearK a s X) = X := by
  funext c i
  by_cases h : c = a
  · subst h
    have h1 : ∀ b, (-s) b * shearK c s X b i = -(s b * X b i) := by
      intro b
      by_cases hb : b = c
      · subst hb
        simp [hs]
      · simp [shearK, Function.update, hb]
    simp only [shearK, Function.update_self]
    have h2 : ∑ b, (-s) b * (Function.update X c (fun i => X c i + ∑ b, s b * X b i)) b i = -∑ b, s b * X b i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => h1 b
    rw [h2]
    ring
  · simp [shearK, Function.update, h]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem avgInf_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (c : HermR (Ainf F) σ n) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Measurable φ ∧ Integrable φ (minf c) ∧ ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Integrable (fun X => φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hM d b lam hinf minf hminf c φ hφ
  classical
  have hlam : lam.IsAddHaarMeasure := hinf.1
  obtain ⟨ρ0, e, hρ0, he, hρe, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  obtain ⟨τ₀, κ, hco⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hCM ρ0 e hρ0 he hρe
  obtain ⟨hκ, -, hκa⟩ := isSplitK_of_isCoord hCM hco
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  haveI i1 : LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hLH
  haveI i2 : SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hSH
  haveI i3 : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := hT2H
  haveI i4 : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI i5 : LocallyCompactSpace (HermR (Ainf F) σ n) := hLH
  haveI i6 : SecondCountableTopology (HermR (Ainf F) σ n) := hSH
  haveI i7 : T2Space (HermR (Ainf F) σ n) := hT2H
  haveI i8 : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨halg, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hCM M J hJ (Ainf F) n
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμdef
  set ν := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n with hνdef
  set Q := GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (n := n) with hQdef
  have hQc : Continuous Q := by
    obtain ⟨G, hGc, hGe⟩ := hG M J hJ
    have : Q = G := by
      funext X
      exact Subtype.ext (hGe X)
    rw [this]
    exact hGc
  have hQv : ∀ X, (Q X : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = gramR (Ainf F) σ J X := fun _ => rfl
  obtain ⟨hbc, hUo, hgood⟩ := GlobalTheory.T.good_set_compact_linearly_independent (Ainf F ⊗[F] E) (NumberField.InfinitePlace F) κ hκ n M
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨C₀, hC₀, hden⟩ := GlobalTheory.T.archimedean_compact_set_density_bounded F E σ hCM M J hJ n hn hM 2 b lam hlam (boxK κ fun _ _ => 1) (hbc _)
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E), Continuous fun S : HermR (Ainf F) σ n =>
      HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) h * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τg : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun g S =>
    ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, hmem S g⟩
  have hτm : ∀ g, Measurable (τg g) := fun g => ((hcj g).subtype_mk _).measurable
  have hτq : ∀ g X, Q (GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) = τg g (Q X) := fun g X => Subtype.ext (halg X g)
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → Ainf F ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  have hsh : ∀ (S : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 →
      DenLE μ ν Q S C → DenLE μ ν Q (shearK a s '' S) C := by
    intro S C a s hs hS
    have hsn : (-s) a = 0 := by simp [hs]
    have hcs : ∀ s' : Fin n → Ainf F ⊗[F] E,
        Continuous (shearK a s' : (Fin n → Fin M → Ainf F ⊗[F] E) → _) := by
      intro s'
      have : (shearK a s' : (Fin n → Fin M → Ainf F ⊗[F] E) → _) =
          fun X => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X (shearM a s') := funext fun X => shearK_eq_rmul _ a s' X
      rw [this]
      exact hrc _
    let eT : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      { toFun := shearK a s
        invFun := shearK a (-s)
        left_inv := fun X => shearK_neg a s hs X
        right_inv := fun X => by
          have := shearK_neg a (-s) hsn X
          rwa [neg_neg] at this
        continuous_toFun := hcs s
        continuous_invFun := hcs (-s) }
    have hT : MeasurableEmbedding (shearK a s : (Fin n → Fin M → Ainf F ⊗[F] E) → _) := eT.measurableEmbedding
    have hμ' : μ.map (shearK a s) = (1 : ℝ≥0) • μ := by
      rw [one_smul]
      exact GlobalTheory.T.shear_preserves_archimedean_haar F E σ hCM n M 2 b lam hlam a s hs
    have hν' : ν.map (τg (shearM a s)) = (1 : ℝ≥0) • ν := by
      rw [one_smul]
      exact GlobalTheory.T.shear_pushforward_hermitian_measure F E σ hCM n 2 b lam hlam a s hs _ (hτm _) fun S => rfl
    have := denLE_image hT (hτm (shearM a s)) (fun X => by rw [shearK_eq_rmul]; exact hτq _ X) one_ne_zero hμ' hν' hS
    have e1 : (((1 : ℝ≥0)⁻¹ * 1 : ℝ≥0) : ℝ≥0∞) * C = C := by simp
    rw [e1] at this
    exact this
  have hbox : ∀ r : Fin n → NumberField.InfinitePlace F → ℝ, (∀ a w, 0 < r a w) →
      DenLE μ ν Q (boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n))) := by
    intro r hr
    let t : Fin n → Ainf F := fun a => e.symm (r a)
    let ti : Fin n → Ainf F := fun a => e.symm (fun w => (r a w)⁻¹)
    have het : ∀ a, e (t a) = r a := fun a => e.apply_symm_apply _
    have htt : ∀ a, t a * ti a = 1 := by
      intro a
      apply e.injective
      rw [map_mul, map_one, het]
      funext w
      simp only [ti, e.apply_symm_apply, Pi.mul_apply, Pi.one_apply]
      exact mul_inv_cancel₀ (hr a w).ne'
    have ht : ∀ a, IsUnit (t a) := fun a => IsUnit.of_mul_eq_one _ (htt a)
    let al : Ainf F → Ainf F ⊗[F] E := algebraMap (Ainf F) (Ainf F ⊗[F] E)
    have hal1 : ∀ a, al (t a) * al (ti a) = 1 := fun a => by
      simp only [al]
      rw [← map_mul, htt, map_one]
    let g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) := Matrix.diagonal fun a => al (t a)
    let T : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E) := fun X a i => al (t a) * X a i
    have hTr : ∀ X, T X = GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g := by
      intro X
      funext a i
      simp [T, g, GlobalTheory.CompanionTheory.SW.rmul, Matrix.diagonal_apply, mul_comm]
    have hTc : ∀ u : Fin n → Ainf F ⊗[F] E, Continuous fun (X : Fin n → Fin M → Ainf F ⊗[F] E) a i => u a * X a i := by
      intro u
      refine continuous_pi fun a => continuous_pi fun i => ?_
      exact continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
    let eT : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      { toFun := T
        invFun := fun X a i => al (ti a) * X a i
        left_inv := fun X => by
          funext a i
          simp only [T]
          rw [← mul_assoc, mul_comm (al (ti a)), hal1, one_mul]
        right_inv := fun X => by
          funext a i
          simp only [T]
          rw [← mul_assoc, hal1, one_mul]
        continuous_toFun := hTc _
        continuous_invFun := hTc _ }
    have hT : MeasurableEmbedding T := eT.measurableEmbedding
    have hsal : ∀ x : Ainf F, sigR (Ainf F) σ (al x) = al x := by
      intro x
      simp [al, sigR, Algebra.TensorProduct.algebraMap_apply]
    have hτe : ∀ (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) i j,
        (τg g S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j =
          al (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * al (t j) := by
      intro S i j
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g = g := by
        ext p q
        by_cases hpq : p = q
        · subst hpq
          simp [HeckeCharacterZeroLocus.SiegelWeilU.cT, g, hsal]
        · have hqp : q ≠ p := fun h => hpq h.symm
          simp [HeckeCharacterZeroLocus.SiegelWeilU.cT, g, Matrix.diagonal_apply, hpq, hqp]
      show (HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g) i j = _
      rw [h1]
      simp only [g, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hμ' := GlobalTheory.T.archimedean_measure_scaling_by_units F E σ hCM n M 2 b lam hlam e he t ht
    have hν' := GlobalTheory.T.archimedean_hermitian_scaling_by_units F E σ hCM n 2 b lam hlam e he t ht (τg g) (hτm g) hτe
    set P : Fin n → ℝ≥0 := fun a => ∏ w, ‖e (t a) w‖₊ with hP
    have hP0 : ∀ a, P a ≠ 0 := by
      intro a
      refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
      rw [het]
      exact nnnorm_ne_zero_iff.2 (hr a w).ne'
    have ha : (∏ a, ((P a)⁻¹) ^ (2 * M)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (inv_ne_zero (hP0 a))
    have hq : ∀ X, Q (T X) = τg g (Q X) := fun X => by rw [hTr]; exact hτq g X
    have h1 := denLE_image hT (hτm g) hq ha hμ' hν' hden
    have himg : T '' (boxK κ fun _ _ => 1) = boxK κ r := by
      have hκn : ∀ (a : Fin n) (x : Ainf F ⊗[F] E) w, ‖κ (al (t a) * x) w‖ = r a w * ‖κ x w‖ := by
        intro a x w
        rw [map_mul, Pi.mul_apply, norm_mul, show κ (al (t a)) w = (e (t a) w : ℂ) from hκa _ _, het,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr a w)]
      ext X
      constructor
      · rintro ⟨Z, hZ, rfl⟩ a i w
        show ‖κ (al (t a) * Z a i) w‖ ≤ r a w
        rw [hκn]
        have := hZ a i w
        nlinarith [hr a w, norm_nonneg (κ (Z a i) w)]
      · intro hX
        refine ⟨eT.symm X, ?_, eT.apply_symm_apply X⟩
        intro a i w
        have h2 : T (eT.symm X) = X := eT.apply_symm_apply X
        have h3 := hX a i w
        rw [← h2] at h3
        change ‖κ (al (t a) * (eT.symm X) a i) w‖ ≤ r a w at h3
        rw [hκn] at h3
        have := hr a w
        by_contra hc
        push_neg at hc
        nlinarith
    rw [himg] at h1
    have hconst : (((∏ a, ((P a)⁻¹) ^ (2 * M))⁻¹ * ∏ a, ((P a)⁻¹) ^ (2 * n) : ℝ≥0) : ℝ≥0∞) * C₀ =
        C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)) := by
      have hk : ∀ a, ((P a)⁻¹ ^ (2 * M))⁻¹ * (P a)⁻¹ ^ (2 * n) = P a ^ (2 * (M - n)) := by
        intro a
        obtain ⟨k, rfl⟩ : ∃ k, M = n + k := ⟨M - n, by omega⟩
        have hx := hP0 a
        rw [Nat.add_sub_cancel_left, mul_add, inv_pow, inv_inv, pow_add, inv_pow, mul_comm,
          inv_mul_cancel_left₀ (pow_ne_zero _ hx)]
      have h2 : ((∏ a, ((P a)⁻¹) ^ (2 * M))⁻¹ * ∏ a, ((P a)⁻¹) ^ (2 * n) : ℝ≥0) = ∏ a, P a ^ (2 * (M - n)) := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun a _ => hk a
      rw [h2, mul_comm]
      congr 1
      push_cast
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hP]
      push_cast
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [het]
      congr 1
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (hr a w).le]
      congr 1
      ext
      simp [abs_of_pos (hr a w)]
    rw [hconst] at h1
    exact h1
  have hbm : ∀ r : Fin n → NumberField.InfinitePlace F → ℝ, MeasurableSet (boxK (M := M) κ r) :=
    fun r => (hbc r).measurableSet
  obtain ⟨hφc, hφi, ⟨B, hB⟩, hdec⟩ := GlobalTheory.T.schwartz_arch_continuous_integrable F E σ hCM κ hκ n M 2 b lam hlam φ hφ
  have hdom : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set (Fin n → Fin M → Ainf F ⊗[F] E), IsCompact A ∧
      A ⊆ {X | LinearIndependent (Ainf F ⊗[F] E) X} ∧ ∀ Y, MeasurableSet Y →
        ∫⁻ X in Aᶜ ∩ Q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
    intro ε hε
    obtain ⟨R, ε', h0, h⟩ := dom_generic κ hn hM hC₀ hbox hsh hQc.measurable hbm hB hdec hε
    exact ⟨goodK κ R ε', (hgood R ε' h0).1, (hgood R ε' h0).2, h⟩
  let Q' : (Fin n → Fin M → Ainf F ⊗[F] E) → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n := Q
  have hQc' : Continuous Q' := hQc
  have key := GlobalTheory.T.disintegration_along_continuous_quotient_map (Fin n → Fin M → Ainf F ⊗[F] E) (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n)
    (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) μ ν (gramR (Ainf F) σ J) Subtype.val Q' _ minf hUo hQc'
    Subtype.val_injective hQv hminf φ hφc hφi hdom c
  refine ⟨hφc.measurable, key.1, fun ρ hρ hs => ?_⟩
  have hgt : ∀ k X, gramTest (Ainf F) σ J c (ρ k) X = ρ k (c - Q X) := by
    intro k X
    have hm : (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) - gramR (Ainf F) σ J X ∈ HermR (Ainf F) σ n := (c - Q X).2
    unfold gramTest
    exact dif_pos hm
  let r : ℕ → HermR (Ainf F) σ n → ℝ := fun k y => ρ k (c - y)
  have hr1 : ∀ k, Continuous (r k) := fun k => (hρ k).1.comp (continuous_const.sub continuous_id)
  have hr2 : ∀ k, HasCompactSupport (r k) := fun k => (hρ k).2.1.comp_homeomorph (Homeomorph.subLeft c)
  have hint : ∀ k, ∫ y, r k y ∂ν = ∫ y, ρ k y ∂ν := fun k => integral_sub_left_eq_self (G := HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) (ρ k) ν c
  have hrk : ∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν :=
    fun k => ⟨hr1 k, hr2 k, fun y => (hρ k).2.2.1 _, by rw [hint]; exact (hρ k).2.2.2⟩
  have hrs : Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have h0 : (fun u => c - u) ⁻¹' t ∈ nhds (0 : HermR (Ainf F) σ n) := by
      have : Continuous fun u : HermR (Ainf F) σ n => c - u := continuous_const.sub continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using ht)
    filter_upwards [(Filter.tendsto_smallSets_iff.1 hs) _ h0] with k hk y hy
    have h1 : tsupport (r k) = (Homeomorph.subLeft c) ⁻¹' tsupport (ρ k) :=
      tsupport_comp_eq_preimage (ρ k) (Homeomorph.subLeft c)
    rw [h1] at hy
    have := hk hy
    simpa using this
  have hlim := key.2 r hrk hrs
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := (hr2 k).exists_bound_of_continuous (hr1 k)
    refine (hφi.norm.mul_const C).mono' ?_ (Filter.Eventually.of_forall fun X => ?_)
    · refine hφc.aestronglyMeasurable.mul ?_
      have : (fun X => ((gramTest (Ainf F) σ J c (ρ k) X : ℝ) : ℂ)) = fun X => ((r k (Q X) : ℝ) : ℂ) := by
        funext X
        rw [hgt]
      rw [this]
      exact (Complex.continuous_ofReal.comp ((hr1 k).comp hQc)).aestronglyMeasurable
    · rw [norm_mul, hgt, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · refine (hlim.congr fun k => ?_)
    rw [hint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show φ X * ((r k (Q X) : ℝ) : ℂ) = φ X * ((gramTest (Ainf F) σ J c (ρ k) X : ℝ) : ℂ)
    rw [hgt]

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
