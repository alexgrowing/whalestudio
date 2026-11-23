import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrab
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IkedaSch

open GlobalTheory.Core.Rk.SWLaw (zeroSp dblDec)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem trace_incA (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem trace_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) : (rat M : Mx D ρ ρ).trace = incA D M.trace := by
  simp only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply, map_sum]

def chi (ψ : AddChar (AF D.host.F) ℂ) {k ρ : ℕ} (M : Matrix (Fin k) (Fin ρ) D.host.E) (z : Mx D k ρ) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (adj z ⬝ (rat M : Mx D k ρ)).trace))

theorem chi_add {k ρ : ℕ} (M : Matrix (Fin k) (Fin ρ) D.host.E) (z z' : Mx D k ρ) :
    chi ψ M (z + z') = chi ψ M z * chi ψ M z' := by
  simp only [chi, adj_add, Matrix.add_mul, Matrix.trace_add, mul_add, map_add, AddChar.map_add_eq_mul]

theorem chi_rat (hψ : IsCharAF D.host.F ψ) {k ρ : ℕ} (M γ : Matrix (Fin k) (Fin ρ) D.host.E) : chi ψ M (rat γ) = 1 := by
  rw [chi, ← rat_conjTranspose, ← rat_mul, trace_rat, ← map_mul, trace_incA]
  exact hψ.2.2.1 _

theorem exists_chi_ne (hψ : IsCharAF D.host.F ψ) {k ρ : ℕ} {M : Matrix (Fin k) (Fin ρ) D.host.E} (hM : M ≠ 0) :
    ∃ z, chi ψ M z ≠ 1 := by
  obtain ⟨a, ha⟩ := hψ.2.2.2
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (Matrix.ext h)
  obtain ⟨z, hz⟩ := Algebra.trace_surjective D.host.F D.host.E 1
  refine ⟨adj (Matrix.single j i (algebraMap (AF D.host.F) (AE D) a * incA D (z * (D.host.xi0 * M i j)⁻¹))), ?_⟩
  have h0 : D.host.xi0 * M i j ≠ 0 := mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) hij
  have e : incA D D.host.xi0 * (algebraMap (AF D.host.F) (AE D) a * incA D (z * (D.host.xi0 * M i j)⁻¹) * incA D (M i j)) =
      a • incA D z := by
    have e0 : D.host.xi0 * (z * (D.host.xi0 * M i j)⁻¹ * M i j) = z := by field_simp [GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D]
    rw [Algebra.smul_def]
    conv_rhs => rw [← e0, map_mul, map_mul]
    ring
  rw [chi, adj_adj, Matrix.trace_single_mul, smul_eq_mul, show (rat M : Mx D k ρ) i j = incA D (M i j) from rfl, e,
    map_smul, trace_incA, hz, map_one, smul_eq_mul, mul_one]
  exact ha

theorem integral_chi (hψ : IsCharAF D.host.F ψ) {k ρ : ℕ} (M : Matrix (Fin k) (Fin ρ) D.host.E) {μ : Measure (Mx D k ρ)}
    {𝓕 : Set (Mx D k ρ)} (hμ : IsCovolOne (ratMx D k ρ) μ 𝓕) : ∫ z in 𝓕, chi ψ M z ∂μ = if M = 0 then 1 else 0 := by
  split_ifs with hM
  · subst hM
    simp only [chi, rat_zero, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero, AddChar.map_zero_eq_one]
    rw [setIntegral_const, Measure.real, hμ.2.2, ENNReal.toReal_one, one_smul]
  · obtain ⟨z, hz⟩ := exists_chi_ne hψ hM
    have h := covolOne_integral_add hμ (chi ψ M) (fun γ ⟨δ, hδ⟩ a => by
      rw [chi_add, ← show rat δ = γ from hδ, chi_rat hψ, one_mul]) z
    simp only [chi_add, integral_mul_const] at h
    by_contra h0
    exact hz ((mul_eq_left₀ h0).1 h)

theorem continuous_chi (hψ : IsCharAF D.host.F ψ) {k ρ : ℕ} (T : HSp D) {S : HSp D} (e : HypDec S (zeroSp D) ρ)
    (J : Matrix (Fin T.rank) (Fin k) D.host.E) (η : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    (∀ z : Mx D k ρ, ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat J ⬝ z))) = chi ψ (Jᴴ * T.gram * η) z) ∧
      Continuous (chi ψ (Jᴴ * T.gram * η)) := by
  have h1 : ∀ z : Mx D k ρ, ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat J ⬝ z))) = chi ψ (Jᴴ * T.gram * η) z := fun z => by
    have h := e.hO_ext T (rat η) 0 0 (rat J ⬝ z) 0 0
    simp only [map_zero, zero_add, add_zero, hO_eq_trace (zeroSp D), Matrix.mul_zero, Matrix.trace_zero] at h
    rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, chi, rat_mul, rat_mul,
      rat_conjTranspose, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rfl
  refine ⟨h1, ?_⟩
  rw [← funext h1]
  simp only [← Check.symplOH_add_self, AddChar.map_add_eq_mul]
  have hc : Continuous fun z : Mx D k ρ => ψ (symplOH S T (e.extX T (rat η)) (e.extY T (rat J ⬝ z))) :=
    hψ.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_const
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const))
  exact hc.mul hc

theorem countable_mat (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact Function.Injective.countable (f := fun ξ => (⟨rat ξ, rat_mem ξ⟩ : ratMx D m n))
    fun a b h => rat_injective (congrArg Subtype.val h)

theorem integral_series (hψ : IsCharAF D.host.F ψ) {k ρ : ℕ} {T S : HSp D} (e : HypDec S (zeroSp D) ρ)
    (J : Matrix (Fin T.rank) (Fin k) D.host.E) {μ : Measure (Mx D k ρ)} {𝓕 : Set (Mx D k ρ)}
    (hμ : IsCovolOne (ratMx D k ρ) μ 𝓕) (c : Matrix (Fin T.rank) (Fin ρ) D.host.E → ℂ) (hc : Summable fun η => ‖c η‖) :
    ∫ (z : Mx D k ρ) in 𝓕, ∑' η, ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat J ⬝ z))) * c η ∂μ =
      ∑' η, if Jᴴ * T.gram * η = 0 then c η else 0 := by
  haveI := countable_mat (D := D) T.rank ρ
  haveI : BorelSpace (Mx D k ρ) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hn : ∀ η (z : Mx D k ρ), ‖ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat J ⬝ z))) * c η‖ = ‖c η‖ := fun η z => by
    rw [norm_mul, hψ.2.1, one_mul]
  rw [← integral_tsum_of_summable_integral_norm]
  · refine tsum_congr fun η => ?_
    simp only [(continuous_chi hψ T e J η).1]
    rw [integral_mul_const, integral_chi hψ _ hμ]
    split_ifs <;> simp
  · intro η
    refine Integrable.of_bound ?_ ‖c η‖ (.of_forall fun z => (hn η z).le)
    simp only [(continuous_chi hψ T e J η).1]
    exact ((continuous_chi hψ T e J η).2.mul continuous_const).measurable.aestronglyMeasurable
  · simp only [hn]
    simpa only [setIntegral_const, Measure.real, hμ.2.2, ENNReal.toReal_one, one_smul] using hc

theorem sFinite_of_prob {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] : SFinite μ := inferInstance

theorem continuous_mean {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [SecondCountableTopology Y] (μ : Measure X) [IsProbabilityMeasure μ] (F : X × Y → ℂ)
    (hF : Continuous F) (C : ℝ) (hC : ∀ p, ‖F p‖ ≤ C) :
    (Continuous fun y => ∫ x, F (x, y) ∂μ) ∧ ∀ y, ‖∫ x, F (x, y) ∂μ‖ ≤ C :=
  ⟨continuous_of_dominated (bound := fun _ => C)
      (fun _ => (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun _ => .of_forall fun _ => hC _) (integrable_const C)
      (.of_forall fun _ => hF.comp (continuous_const.prodMk continuous_id)),
    fun y => by simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => F (x, y)) (.of_forall fun _ => hC _)⟩

theorem integral_halves {t ρ : ℕ} {S : HSp D} (e : HypDec S (zeroSp D) ρ) {μ₁ : Measure (Mx D t S.rank)}
    {𝓕₁ : Set (Mx D t S.rank)} (h₁ : IsCovolOne (ratMx D t S.rank) μ₁ 𝓕₁) {μ : Measure (Mx D t ρ)} {𝓕 : Set (Mx D t ρ)}
    (h₂ : IsCovolOne (ratMx D t ρ) μ 𝓕) (h : Mx D t S.rank → ℂ) (hc : Continuous h) (C : ℝ) (hC : ∀ x, ‖h x‖ ≤ C)
    (hp : ∀ γ ∈ ratMx D t S.rank, ∀ x, h (γ + x) = h x) :
    ∫ ξ in 𝓕₁, h ξ ∂μ₁ = ∫ u in 𝓕, ∫ v in 𝓕, h (u ⬝ e.pX + v ⬝ e.pY) ∂μ ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D t S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D t ρ
  haveI : BorelSpace (Mx D t S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t ρ) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (μ₁.restrict 𝓕₁) := ⟨by rw [Measure.restrict_apply_univ, h₁.2.2]⟩
  haveI : IsProbabilityMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h₂.2.2]⟩
  haveI := sFinite_of_prob (μ₁.restrict 𝓕₁)
  haveI := sFinite_of_prob (μ.restrict 𝓕)
  have hL : Continuous fun p : Mx D t ρ × Mx D t ρ => (p.1 ⬝ e.pX + p.2 ⬝ e.pY : Mx D t S.rank) :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  have hI : Integrable (Function.uncurry fun (p : Mx D t ρ × Mx D t ρ) (ξ : Mx D t S.rank) =>
      h (ξ + (p.1 ⬝ e.pX + p.2 ⬝ e.pY))) (((μ.restrict 𝓕).prod (μ.restrict 𝓕)).prod (μ₁.restrict 𝓕₁)) :=
    Integrable.of_bound (hc.comp (continuous_snd.add (hL.comp continuous_fst))).aestronglyMeasurable C
      (.of_forall fun _ => hC _)
  have hs := integral_integral_swap hI
  simp only [covolOne_integral_add h₁ h hp, integral_const, probReal_univ, one_smul] at hs
  rw [hs]
  have key : ∀ ξ : Mx D t S.rank, ∫ p : Mx D t ρ × Mx D t ρ, h (ξ + (p.1 ⬝ e.pX + p.2 ⬝ e.pY))
      ∂(μ.restrict 𝓕).prod (μ.restrict 𝓕) = ∫ u in 𝓕, ∫ v in 𝓕, h (u ⬝ e.pX + v ⬝ e.pY) ∂μ ∂μ := fun ξ => by
    rw [integral_prod (fun p : Mx D t ρ × Mx D t ρ => h (ξ + (p.1 ⬝ e.pX + p.2 ⬝ e.pY))) (Integrable.of_bound (hc.comp (continuous_const.add hL)).aestronglyMeasurable C
      (.of_forall fun _ => hC _))]
    have hξ : ξ = ξ ⬝ e.jX ⬝ e.pX + ξ ⬝ e.jY ⬝ e.pY := by
      have h0 : e.j0 ⬝ e.p0 = 0 := Matrix.ext fun i j => by
        rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← add_zero (e.jX ⬝ e.pX), ← h0, e.sum_eq_one,
        Matrix.mul_one]
    have e1 : ∀ u v : Mx D t ρ, ξ + (u ⬝ e.pX + v ⬝ e.pY) = (u + ξ ⬝ e.jX) ⬝ e.pX + (v + ξ ⬝ e.jY) ⬝ e.pY := fun u v => by
      conv_lhs => rw [hξ]
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    simp only [e1]
    have e2 : ∀ u : Mx D t ρ, ∫ v in 𝓕, h (u ⬝ e.pX + (v + ξ ⬝ e.jY) ⬝ e.pY) ∂μ = ∫ v in 𝓕, h (u ⬝ e.pX + v ⬝ e.pY) ∂μ :=
      fun u => covolOne_integral_add h₂ (fun v => h (u ⬝ e.pX + v ⬝ e.pY)) (fun γ hγ v => by
        rw [Matrix.add_mul, add_left_comm, hp _ (ratMx_mul hγ (rat_mem e.qY) : γ ⬝ e.pY ∈ _)]) _
    simp only [e2]
    exact covolOne_integral_add h₂ (fun u => ∫ v in 𝓕, h (u ⬝ e.pX + v ⬝ e.pY) ∂μ) (fun γ hγ u => by
      simp only [Matrix.add_mul, add_assoc, hp _ (ratMx_mul hγ (rat_mem e.qX) : γ ⬝ e.pX ∈ _)]) _
  simp only [key, integral_const, probReal_univ, one_smul]

theorem integral_unfold {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕)
    (P : Mx D m n → ℂ) (hc : Continuous P) (hP : Integrable P μ) :
    ∫ u in 𝓕, ∑' γ : Matrix (Fin m) (Fin n) D.host.E, P (rat γ + u) ∂μ = ∫ x, P x ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  let ε : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n := Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
    ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun ⟨_, δ, hδ⟩ => ⟨δ, Subtype.ext hδ⟩⟩
  have e1 : ∀ u, ∑' γ : Matrix (Fin m) (Fin n) D.host.E, P (rat γ + u) = ∑' g : ratMx D m n, P (g +ᵥ u) :=
    fun u => ε.tsum_eq fun g => P (g +ᵥ u)
  simp only [e1]
  rw [hμ.2.1.integral_eq_tsum'' P hP, integral_tsum]
  · exact fun g => (hc.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable
  · rw [← hμ.2.1.lintegral_eq_tsum'' fun x => ‖P x‖ₑ]
    exact hP.2.ne

variable {S T T' : HSp D} {ρ t : ℕ} (e : HypDec S (zeroSp D) ρ) (d : HypDec T T' t)

theorem integrable_slice (hψ : IsStdChar D ψ (-1)) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {μ : Measure (Mx D t ρ)} {𝓕 : Set (Mx D t ρ)} (hμ : IsCovolOne (ratMx D t ρ) μ 𝓕) :
    Continuous (fun x : Mx D t ρ => e.mixS T ψ v.μ v.𝓕 f (d.jX ⬝ x) 0) ∧
      Integrable (fun x : Mx D t ρ => e.mixS T ψ v.μ v.𝓕 f (d.jX ⬝ x) 0) μ := by
  have hc : Continuous (fun x : Mx D t ρ => e.mixS T ψ v.μ v.𝓕 f (d.jX ⬝ x) 0) :=
    (GlobalTheory.Core.Rk.SchInt.mixS_continuous_integrable hψ e v hf 0).1.comp (continuous_const.matrix_mul continuous_id)
  refine ⟨hc, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D t ρ
  haveI : BorelSpace (Mx D t ρ) := ⟨rfl⟩
  haveI := hμ.1
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ t ρ (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun s _ => by
      have e : (fun x : Mx D t ρ => x + s) = fun x => s + x := funext fun x => add_comm x s
      rw [e]; exact map_add_left_eq_self μ s)
  obtain ⟨U, hU, hfU⟩ := hf.level
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.Unf.mixS_le_maj D ψ hψ θ hθ S (zeroSp D) T ρ e v U hU
  obtain ⟨C, hC⟩ := hKN N
  have hfin := ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := C)) ((GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T).1 N f hf)
  have hli : LinearIndependent D.host.E d.e.transpose := by
    have h1 : d.qX * d.e = 1 := d.e'e
    refine Matrix.mulVec_injective_iff.1 fun a b hab => ?_
    have := congrArg (d.qX *ᵥ ·) hab
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  obtain ⟨K', hK', hKK⟩ := GlobalTheory.Unf.MajMeas.maj_rat_le θ T.rank t ρ d.e hli K hK
  obtain ⟨C', hC'⟩ := hKK N
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hI := ((hN K' hK').const_mul C').2
  refine lt_of_le_of_lt (lintegral_mono fun x => (hC f ⟨hf, hfU⟩ (d.jX ⬝ x) 0).trans
    (mul_le_mul_right ((ENNReal.ofReal_le_ofReal (hC' x)).trans (Real.ofReal_le_enorm _)) _)) ?_
  rw [lintegral_const_mul' _ _ hfin]
  exact ENNReal.mul_lt_top hfin.lt_top hI

theorem hasSum_recon (hψ : IsStdChar D ψ (-1)) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (x y : Mx D T.rank ρ) :
    HasSum (fun η : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
      ψ (symplO S T (e.extX T (rat η + x)) (e.extY T y)) * e.mixS T ψ v.μ v.𝓕 f (rat η + x) 0)
      (ψ (symplOH S T (e.extX T x) (e.extY T y)) * f (e.extX T x + e.extY T y)) := by
  have hH := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have h5 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S (zeroSp D) T ρ e v _
    (hH (e.extX T x) _ (hH (e.extY T y) _ hf))).2.2.2.2 0
  simp only [Check.mixS_heis_extX, Check.mixS_heis_extY e v.covol hf] at h5
  simpa only [heisO, map_zero, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add] using h5

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [← Check.symplOH_add_self, GlobalTheory.OrientedHeis.symplOH_add_right]; ring

theorem iso_pair (ξ ξ' : Mx D t S.rank) (w : WO S T') : symplOH S T (d.jX ⬝ ξ) (d.jX ⬝ ξ' + d.j0 ⬝ w) = 0 := by
  rw [GlobalTheory.OrientedHeis.symplOH_add_right]
  exact (congrArg₂ (· + ·) (d.symplOH_incX_incX S ξ ξ') (d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ w)).trans (add_zero 0)

theorem tsum_reindex (G : Matrix (Fin T.rank) (Fin ρ) D.host.E → ℂ) :
    (∑' η, if d.eᴴ * T.gram * η = 0 then (if d.i₀ᴴ * T.gram * η = 0 then G η else 0) else 0) =
      ∑' γ : Matrix (Fin t) (Fin ρ) D.host.E, G (d.e * γ) := by
  have hXe : d.qX * d.e = 1 := d.e'e
  have hinj : Function.Injective fun γ : Matrix (Fin t) (Fin ρ) D.host.E => d.e * γ := fun a b hab => by
    have := congrArg (d.qX * ·) hab
    simpa only [← Matrix.mul_assoc, hXe, Matrix.one_mul] using this
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun γ => ?_
    have a1 : d.eᴴ * T.gram * (d.e * γ) = 0 := by rw [← Matrix.mul_assoc, d.ee, Matrix.zero_mul]
    have a2 : d.i₀ᴴ * T.gram * (d.e * γ) = 0 := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
    exact (if_pos a1).trans (if_pos a2)
  · intro η hη
    have hY : d.eᴴ * T.gram * η = 0 := by by_contra h; exact hη (if_neg h)
    have h0 : d.i₀ᴴ * T.gram * η = 0 := by by_contra h; exact hη (by simp only [if_neg h, ite_self])
    refine ⟨d.qX * η, ?_⟩
    have := congrArg (· * η) d.sum_eq_one_rat
    simpa only [Matrix.add_mul, HypDec.q0, HypDec.qY, Matrix.mul_assoc d.e, Matrix.mul_assoc d.i₀, Matrix.mul_assoc d.e',
      Matrix.mul_assoc T'.gram⁻¹, hY, h0, Matrix.mul_zero, add_zero, Matrix.one_mul] using this

set_option maxHeartbeats 1000000 in

theorem inner_mean (hψ : IsStdChar D ψ (-1)) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {μ : Measure (Mx D t ρ)} {𝓕 : Set (Mx D t ρ)} (hμ : IsCovolOne (ratMx D t ρ) μ 𝓕)
    {ν : Measure (Mx D T'.rank ρ)} {𝓨 : Set (Mx D T'.rank ρ)} (hν : IsCovolOne (ratMx D T'.rank ρ) ν 𝓨) (u : Mx D t ρ) :
    ∫ (z : Mx D t ρ) in 𝓕, ∫ (b : Mx D T'.rank ρ) in 𝓨, f (d.jX ⬝ (u ⬝ e.pX + z ⬝ e.pY) + d.j0 ⬝ (b ⬝ e.pY)) ∂ν ∂μ =
      ∑' γ : Matrix (Fin t) (Fin ρ) D.host.E, e.mixS T ψ v.μ v.𝓕 f (d.jX ⬝ (rat γ + u)) 0 := by
  set G : Matrix (Fin T.rank) (Fin ρ) D.host.E → ℂ := fun η => e.mixS T ψ v.μ v.𝓕 f (rat η + d.jX ⬝ u) 0 with hG
  have hs : Summable fun η => ‖G η‖ := by
    have h := summable_norm_iff.2 (hasSum_recon e hψ v hf (d.jX ⬝ u) 0).summable
    simpa only [norm_mul, hψ.1.2.1, one_mul] using h
  have h1 : ∀ (z : Mx D t ρ) (b : Mx D T'.rank ρ), f (d.jX ⬝ (u ⬝ e.pX + z ⬝ e.pY) + d.j0 ⬝ (b ⬝ e.pY)) =
      ∑' η, ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat d.i₀ ⬝ b))) *
        (ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat d.e ⬝ z))) * G η) := fun z b => by
    have h := (hasSum_recon e hψ v hf (d.jX ⬝ u) (d.jX ⬝ z + d.j0 ⬝ b)).tsum_eq
    have h0 : symplOH S T (e.extX T (d.jX ⬝ u)) (e.extY T (d.jX ⬝ z + d.j0 ⬝ b)) = 0 := by
      rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      exact iso_pair d _ _ _
    rw [h0, AddChar.map_zero_eq_one, one_mul] at h
    have e1 : e.extX T (d.jX ⬝ u) + e.extY T (d.jX ⬝ z + d.j0 ⬝ b) =
        d.jX ⬝ (u ⬝ e.pX + z ⬝ e.pY) + d.j0 ⬝ (b ⬝ e.pY) := by
      rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_add, add_assoc]
    rw [← e1, ← h]
    refine tsum_congr fun η => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← symplO_add_right, ← map_add, add_comm (rat d.i₀ ⬝ b),
      map_add (e.extX T), ← Check.symplOH_add_self, ← Check.symplOH_add_self, GlobalTheory.OrientedHeis.symplOH_add_left, h0,
      add_zero]
    rfl
  have h2 : ∀ z : Mx D t ρ, ∫ (b : Mx D T'.rank ρ) in 𝓨, f (d.jX ⬝ (u ⬝ e.pX + z ⬝ e.pY) + d.j0 ⬝ (b ⬝ e.pY)) ∂ν =
      ∑' η, ψ (symplO S T (e.extX T (rat η)) (e.extY T (rat d.e ⬝ z))) *
        (if d.i₀ᴴ * T.gram * η = 0 then G η else 0) := fun z => by
    simp only [h1]
    rw [integral_series hψ.1 e d.i₀ hν _ (by simpa only [norm_mul, hψ.1.2.1, one_mul] using hs)]
    simp only [mul_ite, mul_zero]
  simp only [h2]
  rw [integral_series hψ.1 e d.e hμ _ (hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun η => by
    split_ifs <;> simp)]
  rw [tsum_reindex]
  refine tsum_congr fun γ => ?_
  have a3 : d.jX ⬝ (rat γ + u) = rat (d.e * γ) + d.jX ⬝ u := by rw [Matrix.mul_add, rat_mul]; rfl
  rw [a3]

theorem at_zero (hψ : IsStdChar D ψ (-1)) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {μ₁ : Measure (Mx D t S.rank)} {𝓕₁ : Set (Mx D t S.rank)} (h₁ : IsCovolOne (ratMx D t S.rank) μ₁ 𝓕₁)
    {μ : Measure (Mx D t ρ)} {𝓕 : Set (Mx D t ρ)} (hμ : IsCovolOne (ratMx D t ρ) μ 𝓕)
    {ν : Measure (Mx D T'.rank ρ)} {𝓨 : Set (Mx D T'.rank ρ)} (hν : IsCovolOne (ratMx D T'.rank ρ) ν 𝓨) :
    e.mixS T' ψ ν 𝓨 (ikeda ψ d μ₁ 𝓕₁ f) 0 0 = ∫ x : Mx D t ρ, e.mixS T ψ v.μ v.𝓕 f (d.jX ⬝ x) 0 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D t S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T'.rank ρ
  haveI : BorelSpace (Mx D t S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D T'.rank ρ) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (μ₁.restrict 𝓕₁) := ⟨by rw [Measure.restrict_apply_univ, h₁.2.2]⟩
  haveI : IsProbabilityMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]⟩
  haveI := sFinite_of_prob (μ₁.restrict 𝓕₁)
  haveI := sFinite_of_prob (ν.restrict 𝓨)
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ f hf
  have hc : Continuous fun p : Mx D T'.rank ρ × Mx D t S.rank => f (d.jX ⬝ p.2 + d.j0 ⬝ (p.1 ⬝ e.pY)) :=
    hf.cont.comp ((continuous_const.matrix_mul continuous_snd).add
      (continuous_const.matrix_mul (continuous_fst.matrix_mul continuous_const)))
  have hm := continuous_mean (ν.restrict 𝓨) _ hc C fun _ => hC _
  simp only [Check.mixS_eq e ν, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero, ikeda_apply,
    HypDec.extY_apply]
  rw [integral_integral_swap (f := fun (b : Mx D T'.rank ρ) (ξ : Mx D t S.rank) => f (d.jX ⬝ ξ + d.j0 ⬝ (b ⬝ e.pY)))
    (Integrable.of_bound hc.aestronglyMeasurable C (.of_forall fun _ => hC _)),
    integral_halves e h₁ hμ (fun ξ => ∫ b in 𝓨, f (d.jX ⬝ ξ + d.j0 ⬝ (b ⬝ e.pY)) ∂ν) hm.1 C hm.2]
  · simp only [inner_mean e d hψ v hf hμ hν]
    exact integral_unfold hμ _ (integrable_slice e d hψ v hf hμ).1 (integrable_slice e d hψ v hf hμ).2
  · intro γ hγ ξ
    obtain ⟨δ, hδ⟩ : d.jX ⬝ γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
    refine integral_congr_ae (.of_forall fun b => ?_)
    have h := hf.quasi δ (d.jX ⬝ ξ + d.j0 ⬝ (b ⬝ e.pY))
    rw [show ratW T S δ = d.jX ⬝ γ from hδ, iso_pair, neg_zero, AddChar.map_zero_eq_one, one_mul] at h
    simp only [Matrix.mul_add, add_assoc, h]

theorem sch_ikeda : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)), IsCovolOne (ratL T A) ν 𝓨 → ∀ (ν' : Measure (WO A T')) (𝓨' : Set (WO A T')), IsCovolOne (ratL T' A) ν' 𝓨' → ∀ (μ₁ : Measure (Mx D t (dblSp A).rank)) (𝓕₁ : Set (Mx D t (dblSp A).rank)), IsCovolOne (ratMx D t (dblSp A).rank) μ₁ 𝓕₁ → ∀ (μ₂ : Measure (Mx D t A.rank)) (𝓕₂ : Set (Mx D t A.rank)), IsCovolOne (ratMx D t A.rank) μ₂ 𝓕₂ → ∀ φ, IsThetaFunO ψ (dblSp A) T φ → IsThetaFunO ψ (dblSp A) T' (ikeda ψ d μ₁ 𝓕₁ φ) ∧ sch ψ A T' ν' 𝓨' (ikeda ψ d μ₁ 𝓕₁ φ) = ikS d μ₂ (sch ψ A T ν 𝓨 φ) := by
  intro D ψ hψ A T T' t d ν 𝓨 hν ν' 𝓨' hν' μ₁ 𝓕₁ h₁ μ₂ 𝓕₂ h₂ φ hφ
  refine ⟨(GlobalTheory.MixValues.mixed_values D ψ hψ).2 (dblSp A) T T' t d μ₁ 𝓕₁ h₁ φ hφ 0, funext fun a => ?_⟩
  have hF := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ (dblSp A) T).1 ((dblDec A).extX T (d.j0 ⬝ a)) φ hφ
  have h := at_zero (dblDec A) d hψ ⟨ν, 𝓨, hν⟩ hF h₁ h₂ hν'
  have e1 : (dblDec A).extX T (d.j0 ⬝ a) = d.inc0 (dblSp A) ((dblDec A).extX T' a) := by
    rw [HypDec.extX_apply, HypDec.extX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc]
  simp only [Check.mixS_heis_extX] at h
  rw [e1, ikeda, Check.mixedModelTarget_heisenberg_anisotropic_part, Check.mixS_heis_extX, zero_add] at h
  exact h

end GlobalTheory.IkedaSch

end
