import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPathStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamilyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp only [halfTr, trA, map_add, mul_add]

theorem halfTr_zero : halfTr (0 : AE D) = 0 := by
  simp only [halfTr, trA, map_zero, mul_zero]

theorem continuous_halfTr : Continuous (halfTr : AE D → AF D.host.F) :=
  continuous_const.mul (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D)))

def chi (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D r) : AddChar (hermA D r) ℂ where
  toFun b := ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r)))
  map_zero_eq_one' := by
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (0 : Mx D r r) : Mx D r r))) = 1
    rw [Matrix.mul_zero, Matrix.trace_zero, halfTr_zero, neg_zero]
    exact ψ.map_zero_eq_one
  map_add_eq_mul' x y := by
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (x.1 + y.1) : Mx D r r))) = _
    rw [Matrix.mul_add, Matrix.trace_add, halfTr_add, neg_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D r) (b : hermA D r) :
    chi ψ β b = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := rfl

theorem W_eq_chi (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b * chi ψ β b ∂lam := rfl

theorem norm_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D r) (b : hermA D r) :
    ‖chi ψ β b‖ = 1 := hψ.2.1 _

theorem continuous_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D r) :
    Continuous (chi ψ β) := by
  have h0 : Continuous fun b : hermA D r => Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r) :=
    (continuous_const.matrix_mul continuous_subtype_val).matrix_trace
  exact hψ.1.comp (continuous_halfTr.comp h0).neg

theorem norm_W_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    ‖W ψ V μ lam φ β‖ ≤ ∫ b, ‖Jt ψ V μ φ b‖ ∂lam := by
  rw [W_eq_chi]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [norm_mul, norm_chi hψ, mul_one]

def tq (V : HSp D) (b : Mx D r r) (y : Mx D V.rank r) : AE D :=
  Matrix.trace (HMul.hMul b (inner V y y) : Mx D r r)

theorem tq_add (V : HSp D) (b c : Mx D r r) (y : Mx D V.rank r) : tq V (b + c) y = tq V b y + tq V c y := by
  unfold tq
  rw [Matrix.add_mul, Matrix.trace_add]

theorem continuous_tq (V : HSp D) (b : Mx D r r) : Continuous (tq V b) := by
  have h : Continuous fun y : Mx D V.rank r => (inner V y y : Mx D r r) := by
    unfold GlobalTheory.StdUnn.inner
    exact continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  exact (continuous_const.matrix_mul h).matrix_trace

theorem Jt_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b c : hermA D r) :
    Jt ψ V μ φ (b + c) = ∫ y, φ y * ψ (halfTr (tq V b.1 y)) * ψ (halfTr (tq V c.1 y)) ∂μ := by
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show φ y * ψ (halfTr (tq V (b.1 + c.1) y)) = _
  rw [tq_add, halfTr_add, AddChar.map_add_eq_mul]
  exact (mul_assoc _ _ _).symm

theorem hasDeriv_Jt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D)
    (μ : Measure (Mx D V.rank r)) {φ : Mx D V.rank r → ℂ} (hφ : Integrable φ μ) {M : Mx D V.rank r → ℝ}
    (hM : Measurable M) (hMφ : Integrable (fun y => (M y : ℂ) * φ y) μ) (c : ℝ →+ hermA D r)
    (hc : ∀ (s : ℝ) y, ψ (halfTr (tq V (c s).1 y)) = Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)))
    (b : hermA D r) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Jt ψ V μ φ (b + c t))
      (2 * Real.pi * Complex.I * Jt ψ V μ (fun y => (M y : ℂ) * φ y) (b + c s)) s := by
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hu : Continuous fun y => ψ (halfTr (tq V b.1 y)) :=
    hψ.1.comp (continuous_halfTr.comp (continuous_tq V b.1))
  have hn : ∀ y, ‖ψ (halfTr (tq V b.1 y))‖ = 1 := fun y => hψ.2.1 _
  have hg : Integrable (fun y => φ y * ψ (halfTr (tq V b.1 y))) μ :=
    hφ.norm.mono' (hφ.aestronglyMeasurable.mul hu.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by simp only [norm_mul, hn, mul_one, le_refl])
  have hMg : Integrable (fun y => (M y : ℂ) * (φ y * ψ (halfTr (tq V b.1 y)))) μ := by
    refine hMφ.norm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hMφ.aestronglyMeasurable.mul hu.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)
    · simp only [norm_mul, hn, mul_one, le_refl]
  have h := GlobalTheory.T.fourier_parameter_derivative _ μ (fun y => φ y * ψ (halfTr (tq V b.1 y))) M hM hg hMg s
  have e1 : (fun t : ℝ => Jt ψ V μ φ (b + c t)) = fun t : ℝ => ∫ y, φ y * ψ (halfTr (tq V b.1 y)) *
      Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ := by
    funext t
    rw [Jt_add]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hc])
  have e2 : Jt ψ V μ (fun y => (M y : ℂ) * φ y) (b + c s) = ∫ y, (M y : ℂ) * (φ y * ψ (halfTr (tq V b.1 y))) *
      Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ := by
    rw [Jt_add]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hc, mul_assoc])
  rw [e1, e2]
  exact h

theorem decay_abs {Φ ι : Type} {d : ℕ} (S : Set Φ) (w : Φ → ι → ℂ) (T : Fin d → Φ → Φ) (f : Fin d → ι → ℝ)
    (hb : ∀ φ ∈ S, ∃ C, ∀ i, ‖w φ i‖ ≤ C) (hS : ∀ k, ∀ φ ∈ S, T k φ ∈ S)
    (hR : ∀ k, ∀ φ ∈ S, ∀ i, w (T k φ) i = (f k i : ℂ) * w φ i) (s : Finset (Fin d)) :
    ∀ φ ∈ S, ∃ C, ∀ i, ‖w φ i‖ * ∏ k ∈ s, (1 + f k i ^ 2) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro φ hφ
    obtain ⟨C, hC⟩ := hb φ hφ
    exact ⟨C, fun i => by simpa using hC i⟩
  | insert k s hk ih =>
    intro φ hφ
    obtain ⟨C₁, h₁⟩ := ih φ hφ
    obtain ⟨C₂, h₂⟩ := ih _ (hS k _ (hS k φ hφ))
    refine ⟨C₁ + C₂, fun i => ?_⟩
    have e : ‖w (T k (T k φ)) i‖ = f k i ^ 2 * ‖w φ i‖ := by
      rw [hR k _ (hS k φ hφ), hR k φ hφ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc,
        abs_mul_abs_self, sq]
    have h2 := h₂ i
    rw [e] at h2
    rw [Finset.prod_insert hk]
    nlinarith [h₁ i, h2]

theorem tq_path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (a : HermE D r) (s : ℝ) (y : Mx D V.rank r) :
    tq V (path hσ a s).1 y = rs σ s * tq V (a.1.map (incA D)) y := by
  show Matrix.trace (HMul.hMul (rs σ s • a.1.map (incA D)) (inner V y y) : Mx D r r) = _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

theorem continuous_path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (a : HermE D r) : Continuous (path hσ a) := by
  refine Continuous.subtype_mk (f := fun s : ℝ => rs σ s • a.1.map (incA D)) ?_ _
  exact continuous_pi fun i => continuous_pi fun j => (continuous_rs hσ).mul continuous_const

theorem trace_rat (β a : HermE D r) :
    Matrix.trace (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r) = incA D (Matrix.trace (β.1 * a.1)) := by
  have h : (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r) = (β.1 * a.1).map (incA D) := by
    rw [Matrix.map_mul]
  rw [h]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem chi_path {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    (a β : HermE D r) (s : ℝ) :
    chi ψ β (path hσ a s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * pairF θ α a β : ℝ) : ℂ))) := by
  rw [chi_apply]
  have e : (Matrix.trace (HMul.hMul (β.1.map (incA D)) (path hσ a s).1 : Mx D r r)) =
      rs σ s * incA D (Matrix.trace (β.1 * a.1)) := by
    show Matrix.trace (HMul.hMul (β.1.map (incA D)) (rs σ s • a.1.map (incA D)) : Mx D r r) = _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_rat]
  rw [e, AddChar.map_neg_eq_inv, hph, Complex.exp_neg]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem W_mult {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    {V : HSp D} (hm : 2 * r < V.rank) {μ : Measure (Mx D V.rank r)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕)
    {lam' : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (hlam : IsCovolOneH lam' 𝓖) (a : HermE D r)
    (hmem : ∀ φ ∈ schwartzA θ V.rank r, (fun y => (multM θ α V a y : ℂ) * φ y) ∈ schwartzA θ V.rank r)
    (hMc : Continuous (multM θ α V a))
    {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) (β : HermE D r) :
    W ψ V μ lam' (fun y => (multM θ α V a y : ℂ) * φ y) β = (pairF θ α a β : ℂ) * W ψ V μ lam' φ β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : lam'.IsAddHaarMeasure := hlam.1
  haveI : LocallyCompactSpace (hermA D r) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : SFinite lam' := by
    haveI : SigmaFinite lam' := MeasureTheory.sigmaFinite_of_locallyFinite
    infer_instance
  obtain ⟨𝓕, hF⟩ := hμ
  haveI : μ.IsAddHaarMeasure := hF.1
  have hμ' : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕 := ⟨𝓕, hF⟩
  have hMφ := hmem φ hφ
  have cont : ∀ φ ∈ schwartzA θ V.rank r, Continuous (Jt ψ V μ φ) :=
    fun φ h => GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ' h
  have intg : ∀ φ ∈ schwartzA θ V.rank r, Integrable (Jt ψ V μ φ) lam' := fun φ h =>
    (GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam' 𝓖 hlam _ (cont φ h) (GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ' h)).1
  have hc : ∀ (s : ℝ) y, ψ (halfTr (tq V (path hσ a s).1 y)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * multM θ α V a y : ℝ) : ℂ)) := fun s y => by
    rw [tq_path]
    exact hph _ s
  exact GlobalTheory.T.fourier_one_parameter_integral (hermA D r) lam' (path hσ a) (continuous_path hσ a) _ _ (cont φ hφ) (cont _ hMφ)
    (intg φ hφ) (intg _ hMφ) (chi ψ β) (continuous_chi hψ β) (norm_chi hψ β) (pairF θ α a β)
    (chi_path hσ hph a β)
    (hasDeriv_Jt hψ V μ (GlobalTheory.T.integrable_of_mem_schwartzA D θ hθ _ _ μ φ hφ) hMc.measurable
      (GlobalTheory.T.integrable_of_mem_schwartzA D θ hθ _ _ μ _ hMφ) (path hσ a) hc)

set_option synthInstance.maxHeartbeats 400000 in
theorem W_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    {V : HSp D} {μ : Measure (Mx D V.rank r)} {lam' : Measure (hermA D r)} [lam'.IsAddHaarMeasure]
    (a : HermE D r) {φ : Mx D V.rank r → ℂ} (N : ℕ)
    (hN : ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul
      (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1)
    (β : HermE D r) (hW : W ψ V μ lam' φ β ≠ 0) : ∃ n : ℤ, (N : ℝ) * pairF θ α a β = n := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r r) := i3
  set v : hermA D r := N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1) with hv
  have hper : ∀ b, Jt ψ V μ φ (b + v) = Jt ψ V μ φ b := fun b => by
    rw [Jt_add]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases h : φ y = 0
    · show φ y * _ * _ = φ y * _
      rw [h]
      simp
    · have h1 : ψ (halfTr (tq V v.1 y)) = 1 := hN y h
      show _ = φ y * ψ (halfTr (tq V b.1 y))
      simp only [h1, mul_one]
  have h1 : W ψ V μ lam' φ β = chi ψ β v * W ψ V μ lam' φ β := by
    rw [W_eq_chi, ← integral_const_mul]
    rw [← integral_add_right_eq_self (fun b => Jt ψ V μ φ b * chi ψ β b) v]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    show Jt ψ V μ φ (b + v) * chi ψ β (b + v) = chi ψ β v * (Jt ψ V μ φ b * chi ψ β b)
    rw [hper, AddChar.map_add_eq_mul]
    ring
  have h2 : chi ψ β v = 1 := by
    have : (chi ψ β v - 1) * W ψ V μ lam' φ β = 0 := by
      rw [sub_mul, ← h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hW)
  have h3 : chi ψ β (GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 = 1 := by
    rw [chi_apply]
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r))) = 1
    rw [trace_rat, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, ← map_neg]
    exact hψ.2.2.1 _
  have h4 : chi ψ β v = Complex.exp (((N : ℂ)) * (2 * Real.pi * Complex.I * (pairF θ α a β : ℂ))) := by
    rw [hv, AddChar.map_nsmul_eq_pow, AddChar.map_sub_eq_div, h3, chi_path hσ hph, Complex.exp_nat_mul]
    congr 1
    rw [one_div, ← Complex.exp_neg, neg_neg]
    congr 1
    push_cast
    ring
  rw [h4, Complex.exp_eq_one_iff] at h2
  obtain ⟨n, hn⟩ := h2
  refine ⟨n, ?_⟩
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h5 : ((N : ℝ) * pairF θ α a β : ℝ) = n := by
    have : (((N : ℝ) * pairF θ α a β : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hI
      push_cast
      linear_combination hn
    exact_mod_cast this
  exact h5

end GlobalTheory.CompanionTheory.WSum

theorem GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)) (φ : Mx D V.rank r → ℂ),
    2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) →
    IsCovolOneH lam 𝓖 → φ ∈ schwartzA θ V.rank r → Summable (fun β : HermE D r => W ψ V μ lam φ β) := by
  intro D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨ψ₀, h₀, α, hα0, hα⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hph := GlobalTheory.T.character_along_one_parameter_path D ψ ψ₀ h₀ α hα θ σ hσ
  obtain ⟨d, a, hinj⟩ := GlobalTheory.T.injective_pairing_finite_family D r θ hθ α hα0
  have hq := fun k => GlobalTheory.T.archimedean_multiplier_temperate D r θ hθ α V (a k)
  choose q hqt hqe using hq
  have hcomp : Continuous fun y : Mx D V.rank r => (fun τ i j => compAt θ τ y i j :
      D.what₂.Tau → Fin V.rank → Fin r → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).matrix_elem i j
  have hMc : ∀ k, Continuous (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k)) := fun k => by
    have h1 : Continuous fun y => ((GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℝ) : ℂ) := by
      simp only [hqe k]
      exact (hqt k).1.continuous.comp hcomp
    exact Complex.continuous_re.comp h1
  have hmem : ∀ k, ∀ φ ∈ schwartzA θ V.rank r,
      (fun y => (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℂ) * φ y) ∈ schwartzA θ V.rank r := fun k φ h => by
    simp only [hqe k]
    exact GlobalTheory.T.temperate_multiplier_preserves_schwartz D θ _ _ (q k) (hqt k) φ h
  have hdec := GlobalTheory.CompanionTheory.WSum.decay_abs (schwartzA θ V.rank r : Set (Mx D V.rank r → ℂ))
    (fun φ β => W ψ V μ lam φ β) (fun k φ y => (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℂ) * φ y)
    (fun k β => GlobalTheory.CompanionTheory.WSum.pairF θ α (a k) β)
    (fun φ _ => ⟨_, fun β => GlobalTheory.CompanionTheory.WSum.norm_W_le hψ V μ lam φ β⟩) hmem
    (fun k φ h β => GlobalTheory.CompanionTheory.WSum.W_mult hψ hθ hσ hph hm hμ hlam (a k) (hmem k) (hMc k) h β) Finset.univ φ hφ
  obtain ⟨C, hC⟩ := hdec
  have hlev := fun k => GlobalTheory.T.integral_multiple_path_trivial_character D r V ψ hψ θ σ hσ (a k) φ hφ
  choose Nk hNk hNy using hlev
  refine GlobalTheory.T.summable_of_lattice_decay_of_injective (HermE D r) d _ (fun β k => GlobalTheory.CompanionTheory.WSum.pairF θ α (a k) β) hinj (∏ k, Nk k)
    (Finset.prod_pos fun k _ => hNk k) C hC fun β hW k => ?_
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.WSum.W_int hψ hσ hph (a k) (Nk k) (hNy k) β hW
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nk (Finset.mem_univ k)
  refine ⟨c * n, ?_⟩
  rw [hc]
  push_cast
  rw [mul_comm ((Nk k : ℝ)) (c : ℝ), mul_assoc, hn]
