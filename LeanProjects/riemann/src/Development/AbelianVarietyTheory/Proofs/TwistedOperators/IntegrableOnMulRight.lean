import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.AvgLift

private theorem isFundamentalDomain_preimage_mul_right' {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) (μ : Measure G) [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (a : G) : IsFundamentalDomain Γ ((fun g => g * a) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_right μ a).quasiMeasurePreserving Function.bijective_id
    (fun γ x => mul_assoc (γ : G) x a)

theorem integrableOn_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hi : IntegrableOn Φ 𝓕 μ)
    (a : G) : IntegrableOn (fun g => Φ (g * a)) 𝓕 μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.integrableOn_iff (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact ((measurePreserving_mul_right μ a).integrableOn_comp_preimage
    (MeasurableEquiv.mulRight a).measurableEmbedding).mpr hi

private theorem setIntegral_fd_comp_mul_right_of_invariant {G E : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → E} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.setIntegral_eq (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact (measurePreserving_mul_right μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulRight a).measurableEmbedding Φ 𝓕

theorem setIntegral_average {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (m : Measure K) [IsProbabilityMeasure m] {κ : K → G} (hκ : Continuous κ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hi : IntegrableOn Φ 𝓕 μ) :
    ∫ g in 𝓕, ∫ k, Φ (g * κ k) ∂m ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hjoint : Continuous fun p : G × K => Φ (p.1 * κ p.2) :=
    hc.comp (continuous_fst.mul (hκ.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun g k => Φ (g * κ k)) ((μ.restrict 𝓕).prod m) := by
    refine (integrable_prod_iff' hjoint.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun k => integrableOn_mul_right Γ μ h hΦ hi (κ k)
    · have hn : ∀ k, ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ = ∫ g in 𝓕, ‖Φ g‖ ∂μ := fun k =>
        setIntegral_fd_comp_mul_right_of_invariant Γ μ h (Φ := fun g => ‖Φ g‖)
          (fun γ hγ g => by simp only [hΦ γ hγ g]) (κ k)
      show Integrable (fun k => ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ) m
      simp only [hn]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hs : ∀ k, ∫ g in 𝓕, Φ (g * κ k) ∂μ = ∫ g in 𝓕, Φ g ∂μ := fun k =>
    setIntegral_fd_comp_mul_right_of_invariant Γ μ h hΦ (κ k)
  simp only [hs, integral_const, probReal_univ, one_smul]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  obtain ⟨hu, hcomm⟩ := hκ
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hκu : κᴴ * κ = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc ((M.fr τ)⁻¹)ᴴ, h2, one_mul, ← mul_assoc (M.fr τ) (M.fr τ)⁻¹, h1, one_mul,
    ← mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hcomm, mul_assoc κ, ← mul_assoc κᴴ κ, hκu, one_mul]

theorem continuous_elt {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (τ : D.what₂.Tau) :
    Continuous fun k : Formalism.REAL.KG (M.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (Formalism.REAL.toMK k) := by
  have hK : ∀ k : Formalism.REAL.KG (M.ε τ), Formalism.REAL.toMK k ∈ Formalism.REAL.Kset (M.ε τ) := fun k =>
    (Formalism.REAL.mem_KG (M.ε τ) k).mp k.2
  have hc : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  show Continuous fun k : Formalism.REAL.KG (M.ε τ) => atTau θ T τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ)
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ).comp_continuous
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const)
    (fun k => frame_mem M τ (hK k))

theorem liftInt_eq_sum_average : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (f : WO V W → ℂ) (fs : Fin n → WO V W → ℂ) (F : GA D W → ℂ) (Fs : Fin n → GA D W → ℂ), (∀ i, Continuous (c i)) → IsThetaFunO ψ V W f → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f = ∑ i, c i k • fs i) → IsAutFun W F → (∀ i h, Fs i h = ∫ k, c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ))) → ∀ g, IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν → (∀ i, IntegrableOn (fun h => thetaKO ω g h (fs i) * Fs i h) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO ω) f F g = ∑ i, Lift.liftInt ν 𝓕 (thetaKO ω) (fs i) (Fs i) g := by
  intro D V W S' M' θ ψ χS χT ω ν 𝓕 hθ hW hν h𝓕 τ n c f fs F Fs hc hf hω hF hFs g hi hii
  obtain ⟨hlc, hsc, ht2, hbor, htg, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨hright, -⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν
  have hker := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hW f hf
  have hec : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k) :=
    continuous_elt hθ M' τ
  have hΦinv : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f * F (γ * h) = thetaKO ω g h f * F h := by
    intro γ hγ h
    have h1 := hker.2 1 (GQ V).one_mem γ hγ g h
    rw [one_mul] at h1
    rw [h1, hF.left γ hγ h]
  have hΦc : Continuous fun h => thetaKO ω g h f * F h :=
    (hker.1.comp (continuous_const.prodMk continuous_id)).mul hF.cont
  have hlin : ∀ (h k : GA D W) (u : WO V W → ℂ), thetaKO ω g (h * k) u = thetaKO ω g h (ω (1, k) u) := by
    intro h k u
    show ω (g, h * k) u 0 = ω (g, h) (ω (1, k) u) 0
    have hp : ((g, h * k) : GA D V × GA D W) = (g, h) * (1, k) := by simp
    rw [hp, map_mul]
    rfl
  have hsum : ∀ (h : GA D W) (k : Formalism.REAL.KG (M'.ε τ)),
      thetaKO ω g h (∑ i, c i k • fs i) = ∑ i, c i k * thetaKO ω g h (fs i) := by
    intro h k
    show ω (g, h) (∑ i, c i k • fs i) 0 = ∑ i, c i k * ω (g, h) (fs i) 0
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ h, ∫ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
      F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ)) =
      ∑ i, thetaKO ω g h (fs i) * Fs i h := by
    intro h
    have hexp : ∀ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) =
        ∑ i, thetaKO ω g h (fs i) * (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k))) := by
      intro k
      rw [hlin, hω k, hsum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFk : Continuous fun k : Formalism.REAL.KG (M'.ε τ) =>
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) :=
      hF.cont.comp (continuous_const.mul hec)
    have hint : ∀ i, Integrable (fun k => thetaKO ω g h (fs i) *
        (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)))) (Formalism.REAL.muK (M'.ε τ)) := fun i =>
      integrableOn_univ.mp
        ((continuous_const.mul ((hc i).mul hFk)).continuousOn.integrableOn_compact isCompact_univ)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hFs i h]
  show ∫ h in 𝓕, thetaKO ω g h f * F h ∂ν = ∑ i, ∫ h in 𝓕, thetaKO ω g h (fs i) * Fs i h ∂ν
  refine (setIntegral_average (GQ W) ν h𝓕 (m := Formalism.REAL.muK (M'.ε τ))
    (Φ := fun h => thetaKO ω g h f * F h) hec hΦinv hΦc hi).symm.trans ?_
  rw [← integral_finsetSum _ fun i _ => hii i]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end GlobalTheory.Chain.IoLift.AvgLift

end
