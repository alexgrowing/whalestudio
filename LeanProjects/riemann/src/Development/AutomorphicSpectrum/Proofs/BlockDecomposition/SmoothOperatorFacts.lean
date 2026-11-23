import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpaceCompleteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordLaplacianPowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianCasimirRelationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianPowerCasimirBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusOnSobolevStatement

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ}

theorem isSec_comb (E : KMod n) (c : ℂ) {f f' : Mat n → E.V} (h : IsSec E f) (h' : IsSec E f') :
    IsSec E (fun y => c • f y + f' y) := by
  intro g hg k
  simp only [h g hg k, h' g hg k, map_add, map_smul]

section

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)

theorem word_est (hAE : AlgEst) (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hC : CalcSteps)
    (h : C₀(ℝ, ℂ)) (hh : ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f f' : Mat n → E.V, IsSec E f' → Sob μ f' →
        cls μ f' = F.Φ h (cls μ f) → ‖cls μ (Rw w f')‖ ≤ C * ‖cls μ f‖ := by
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hΩ w
  obtain ⟨-, -, -, -, hCF, -, -, -, -, -, -, -, hOF, hIb, -⟩ := hC
  choose hm hhm using hh
  obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.right_word_laplacian_power_bound) n μ E.V hL hU hR hAE hCF hIb w
  obtain ⟨Q, hQ⟩ := (GlobalTheory.T.laplacian_casimir_relation) n E hR hOF
  choose Cj hCj using (GlobalTheory.T.laplacian_power_casimir_bound) n μ E Q hL hU hR hCF hQ
  refine ⟨|C₁| * ∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖, ?_⟩
  intro f f' hsec hS hcl
  have hsob : ∀ i, Sob μ (Om^[i] f') := by
    intro i
    induction i with
    | zero => exact hS
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact GlobalTheory.CompanionTheory.SobOpsPf.sob_Om ih
  have hit : ∀ i, cls μ (Om^[i] f') = F.Φ (hm i) (cls μ f) := by
    intro i
    induction i with
    | zero =>
      have : hm 0 = h := by ext y; simp [hhm]
      simpa [this] using hcl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hmem : cls μ (Om^[i] f') ∈ Msob μ E.V := Submodule.subset_span ⟨_, hsob i, rfl⟩
      rw [← hΩ _ hmem (hsob i)]
      exact F.omega (hm i) (hm (i + 1)) (fun y => by simp only [hhm]; ring) _ _ ih
  have hn : ∀ i, ‖cls μ (Om^[i] f')‖ ≤ ‖hm i‖ * ‖cls μ f‖ := by
    intro i
    rw [hit]
    exact ((F.Φ (hm i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (F.norm_le _) (norm_nonneg _))
  have hj : ∀ j, ‖cls μ (Lap^[j] f')‖ ≤ (|Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    intro j
    have hs : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ ≤ (∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hn i
    have h0 : 0 ≤ ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc _ ≤ Cj j * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := hCj j f' hS hsec
      _ ≤ |Cj j| * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cj j| * ((∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs : ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ ≤
      (∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hj j
  calc _ ≤ C₁ * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := hC₁ f' hS
    _ ≤ |C₁| * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |C₁| * ((∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

end

theorem smoothOp : SmoothOp := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hS hAE hC hΩ h hh
  have hW := word_est μ E hAE hL hU hR hC h hh Ω T F hΩ
  choose Cw hCw using hW
  obtain ⟨S, Cs, hb⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hkeep := (GlobalTheory.T.functional_calculus_on_sobolev) n μ E Ω T F hL hU hR hS hC hΩ h
  refine ⟨|Cs| * ∑ w ∈ S, |Cw w|, fun x hx => ?_⟩
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose fs hfS hfsec hfcl using hxs
  choose a haS hasec hacl using fun k => hkeep (fs k) (hfS k) (hfsec k)
  have hacl' : ∀ k, cls μ (a k) = F.Φ h (xs k) := fun k => by rw [hacl, hfcl]

  have hdiff : ∀ w k l, ‖cls μ (Rw w (a k)) - cls μ (Rw w (a l))‖ ≤ |Cw w| * ‖xs k - xs l‖ := by
    intro w k l
    have c1 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (haS l) (haS k)
    have c2 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (hfS l) (hfS k)
    have e1 : cls μ (fun y => (-1 : ℂ) • fs l y + fs k y) = xs k - xs l := by
      have := c2.2 []
      simp only [Rw, id] at this
      rw [this, hfcl, hfcl]
      simp [sub_eq_neg_add]
    have e2 : cls μ (fun y => (-1 : ℂ) • a l y + a k y) = F.Φ h (cls μ (fun y => (-1 : ℂ) • fs l y + fs k y)) := by
      have := c1.2 []
      simp only [Rw, id] at this
      rw [this, hacl', hacl', e1, map_sub]
      simp [sub_eq_neg_add]
    have b := hCw w _ _ (isSec_comb E (-1) (hasec l) (hasec k)) c1.1 e2
    rw [c1.2 w, e1] at b
    have e3 : (-1 : ℂ) • cls μ (Rw w (a l)) + cls μ (Rw w (a k)) = cls μ (Rw w (a k)) - cls μ (Rw w (a l)) := by
      simp [sub_eq_neg_add]
    rw [e3] at b
    exact b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hcs : CauchySeq xs := hlim.cauchySeq
  have hcau : ∀ w, CauchySeq fun k => cls μ (Rw w (a k)) := by
    intro w
    rw [Metric.cauchySeq_iff] at hcs ⊢
    intro ε hε
    have hpos : 0 < |Cw w| + 1 := by positivity
    obtain ⟨N, hN⟩ := hcs (ε / (|Cw w| + 1)) (div_pos hε hpos)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := hN k hk l hl
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hdiff w k l
    rw [lt_div_iff₀ hpos] at h1
    nlinarith [norm_nonneg (xs k - xs l), abs_nonneg (Cw w)]
  obtain ⟨b, hbS, hbt, hbp⟩ := (GlobalTheory.T.sobolev_space_complete) n μ E.V hS a haS hcau
  refine ⟨b, hbS, ?_, ?_, ?_⟩
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := by
      have hk : (k.1 : Mat n).det ≠ 0 := by
        intro h0
        have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 k.2)
        rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
        exact zero_ne_one this
      show (g * k.1).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hg hk
    have t1 := hbp _ hgk
    have t2 : Tendsto (fun j => a j (g * k.1)) atTop (𝓝 (E.ρ k⁻¹ (b g))) := by
      simp only [fun j => hasec j g hg k]
      exact ((E.ρ k⁻¹).continuous.tendsto _).comp (hbp g hg)
    exact tendsto_nhds_unique t1 t2
  · have t1 := hbt []
    simp only [Rw, id] at t1
    have t2 : Tendsto (fun k => cls μ (a k)) atTop (𝓝 (F.Φ h x)) := by
      simp only [hacl']
      exact ((F.Φ h).continuous.tendsto _).comp hlim
    exact tendsto_nhds_unique t1 t2
  · have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have t1 : Tendsto (fun k => ‖a k 1‖) atTop (𝓝 ‖b 1‖) := (hbp 1 h1).norm
    have t2 : Tendsto (fun k => (|Cs| * ∑ w ∈ S, |Cw w|) * ‖xs k‖) atTop (𝓝 ((|Cs| * ∑ w ∈ S, |Cw w|) * ‖x‖)) :=
      hlim.norm.const_mul _
    refine le_of_tendsto_of_tendsto' t1 t2 fun k => ?_
    have b1 := hb E.V (a k) (haS k) 1 h1
    have h0 : 0 ≤ ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs : ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ ≤ (∑ w ∈ S, |Cw w|) * ‖xs k‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w _ => ?_
      have := hCw w (fs k) (a k) (hasec k) (haS k) (by rw [hacl', hfcl])
      rw [hfcl] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc _ ≤ Cs * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := b1
      _ ≤ |Cs| * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cs| * ((∑ w ∈ S, |Cw w|) * ‖xs k‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.FcSmooth
