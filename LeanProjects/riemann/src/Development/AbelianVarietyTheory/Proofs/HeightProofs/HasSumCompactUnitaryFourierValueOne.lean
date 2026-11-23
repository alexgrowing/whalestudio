import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsOrthogonalProjectionPolynomialCompactUnitaStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwapStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFunStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory
variable {n : ℕ}

theorem orth_decomp_L (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ polyV ε d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 :=
  GlobalTheory.T.exists_orthogonal_projection_polynomial_compact_unitary ε d p hp

theorem conv_swap_L (ε : Fin n → Bool) (e q g : KG ε → ℂ) (he : Continuous e) (hq : Continuous q)
    (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) :=
  GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap ε e q g he hq hg

theorem eq_zero_of_orth_L (ε : Fin n → Bool) (h : KG ε → ℂ) (hh : Continuous h)
    (ho : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) : h = 0 :=
  GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun ε h hh ho

theorem integrable_of_cont (ε : Fin n → Bool) {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem firstCountable_KG (ε : Fin n → Bool) : FirstCountableTopology (KG ε) :=
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  ((isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).isInducing.firstCountableTopology

theorem continuous_param (ε : Fin n → Bool) {F : KG ε → KG ε → ℂ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun a => ∫ k, F a k ∂(muK ε) := by
  haveI := firstCountable_KG ε
  have := continuous_parametric_integral_of_continuous (μ := muK ε) hF (s := Set.univ) isCompact_univ
  simpa [Measure.restrict_univ] using this

theorem sum_ker_poly (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) :
    ∀ d, ∀ p ∈ polyV ε d, ∑ i ∈ Finset.range (d + 1), ∫ k, e i k * p k ∂(muK ε) = p 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    exact (he 0).2.2 p hp (fun q hq => by simp [lowV] at hq; simp [hq])
  | succ d ih =>
    intro p hp
    obtain ⟨p', hp', horth⟩ := orth_decomp_L ε d p (continuous_of_mem hp)
    have hp'' : (fun k => p k - p' k) ∈ polyV ε (d + 1) :=
      sub_mem hp (polyV_mono ε (Nat.le_succ d) hp')
    have hcp : Continuous p := continuous_of_mem hp
    have hcp' : Continuous p' := continuous_of_mem hp'
    have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
    have hsplit : ∀ i, ∫ k, e i k * p k ∂(muK ε) =
        ∫ k, e i k * p' k ∂(muK ε) + ∫ k, e i k * (p k - p' k) ∂(muK ε) := by
      intro i
      rw [← integral_add (integrable_of_cont ε (f := fun k => e i k * p' k) ((hce i).mul hcp'))
        (integrable_of_cont ε (f := fun k => e i k * (p k - p' k)) ((hce i).mul (hcp.sub hcp')))]
      congr 1; funext k; ring
    rw [Finset.sum_range_succ, hsplit (d + 1), Finset.sum_congr rfl (fun i _ => hsplit i),
      Finset.sum_add_distrib, ih p' hp']
    have h0 : ∫ k, e (d + 1) k * p' k ∂(muK ε) = 0 := (he (d + 1)).2.1 p' hp'
    have h1 : ∫ k, e (d + 1) k * (p k - p' k) ∂(muK ε) = p 1 - p' 1 :=
      (he (d + 1)).2.2 _ hp'' (fun q hq => horth q hq)
    have h2 : ∀ i ∈ Finset.range (d + 1), ∫ k, e i k * (p k - p' k) ∂(muK ε) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hs : (fun k => star (e i k)) ∈ polyV ε d := polyV_mono ε hi' (star_mem (he i).1)
      have := horth _ hs
      simpa using this
    rw [Finset.sum_eq_zero h2, h0, h1]
    ring

theorem ker_vanish (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) {d i : ℕ} (hi : d < i)
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : ∫ k, e i k * p k ∂(muK ε) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (he (j + 1)).2.1 p (polyV_mono ε (by omega) hp)

theorem hasSum_kFourier (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i))
    (g : KG ε → ℂ) (hg : Continuous g) (b : ℕ → ℝ) (hb : Summable b)
    (hbd : ∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) :
    HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
  set P : ℕ → KG ε → ℂ := fun i k' => ∫ k, e i k * g (k' * k) ∂(muK ε) with hPdef
  have hPc : ∀ i, Continuous (P i) := fun i =>
    continuous_param ε (F := fun k' k => e i k * g (k' * k))
      (((hce i).comp continuous_snd).mul (hg.comp (continuous_fst.mul continuous_snd)))
  have hsum : ∀ k', Summable (fun i => P i k') := fun k' => Summable.of_norm_bounded hb (fun i => hbd i k')
  set u : KG ε → ℂ := fun k' => ∑' i, P i k' with hudef
  have hu : Continuous u := continuous_tsum hPc hb hbd
  have key : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (u k - g k) ∂(muK ε) = 0 := by
    intro d q hq
    have hcq : Continuous q := continuous_of_mem hq
    obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖star (q k)‖ ≤ M := by
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_star.comp hcq)).isBounded.exists_norm_le
      exact ⟨M, fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    have hint : ∀ i, Integrable (fun k => star (q k) * P i k) (muK ε) := fun i =>
      integrable_of_cont ε ((continuous_star.comp hcq).mul (hPc i))
    have hnorm : ∀ i, ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ M * b i := by
      intro i
      calc ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ ∫ _k, M * b i ∂(muK ε) := by
            refine integral_mono (hint i).norm (integrable_const _) (fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (hM k) (hbd i k) (norm_nonneg _) ((norm_nonneg _).trans (hM k))
        _ = M * b i := by simp
    have hsn : Summable fun i => ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) :=
      Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) hnorm (hb.mul_left M)
    have e1 : ∫ k, star (q k) * u k ∂(muK ε) = ∑' i, ∫ k, star (q k) * P i k ∂(muK ε) := by
      rw [integral_tsum_of_summable_integral_norm hint hsn]
      congr 1; funext k
      rw [hudef]; simp only
      exact (tsum_mul_left).symm
    set r : ℕ → KG ε → ℂ := fun i y => ∫ x, e i x * star (q (y * x⁻¹)) ∂(muK ε) with hrdef
    have hpy : ∀ y, (fun x => star (q (y * x⁻¹))) ∈ polyV ε d := fun y =>
      star_mem (inv_mem (φ := fun k => q (y * k)) (mul_left_mem y hq))
    have hrc : ∀ i, Continuous (r i) := fun i =>
      continuous_param ε (F := fun y x => e i x * star (q (y * x⁻¹)))
        (((hce i).comp continuous_snd).mul (continuous_star.comp (hcq.comp (continuous_fst.mul continuous_snd.inv))))
    have e2 : ∀ i, ∫ k, star (q k) * P i k ∂(muK ε) = ∫ y, g y * r i y ∂(muK ε) := fun i =>
      conv_swap_L ε (e i) q g (hce i) hcq hg
    have hr0 : ∀ i ∉ Finset.range (d + 1), ∫ y, g y * r i y ∂(muK ε) = 0 := by
      intro i hi
      have hi' : d < i := by simpa using hi
      have : ∀ y, r i y = 0 := fun y => ker_vanish ε e he hi' (hpy y)
      simp [this]
    have hrs : ∀ y, ∑ i ∈ Finset.range (d + 1), r i y = star (q y) := by
      intro y
      have := sum_ker_poly ε e he d _ (hpy y)
      simp only [hrdef]
      simpa using this
    have e3 : ∫ k, star (q k) * u k ∂(muK ε) = ∫ k, star (q k) * g k ∂(muK ε) := by
      rw [e1, tsum_congr e2, tsum_eq_sum hr0, ← integral_finset_sum]
      · congr 1; funext y
        rw [← Finset.mul_sum, hrs y, mul_comm]
      · intro i _
        exact integrable_of_cont ε (hg.mul (hrc i))
    have hsub : (fun k => star (q k) * (u k - g k)) = fun k => star (q k) * u k - star (q k) * g k := by
      funext k; ring
    rw [hsub, integral_sub (integrable_of_cont ε (f := fun k => star (q k) * u k) ((continuous_star.comp hcq).mul hu))
      (integrable_of_cont ε (f := fun k => star (q k) * g k) ((continuous_star.comp hcq).mul hg)), e3, sub_self]
  have hzero := eq_zero_of_orth_L ε (fun k => u k - g k) (hu.sub hg) key
  have h1 : u 1 = g 1 := sub_eq_zero.1 (congrFun hzero 1)
  have h2 : u 1 = ∑' i, ∫ k, e i k * g k ∂(muK ε) := by simp [hudef, hPdef]
  rw [← h1, h2]
  have := (hsum 1).hasSum
  simpa [hPdef] using this

end GlobalTheory.KFourier
