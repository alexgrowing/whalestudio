import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped NumberField.AdeleRing

private theorem nn_zero {K : Type} [Field K] [NumberField K] : (nn (K := K) 0) = 1 := unipOne_zero 2

private theorem lv_left {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ} (hP : PFun F) (m₂ : G1 K 2) (s : ℝ)
    (γ : G1 K 2) (hγ : γ ∈ Gam K 2) (m : G1 K 2) (g : G1 K (2 + 2)) :
    F (lv m₂ (γ * m) s * g) = F (lv m₂ m s * g) := by
  have hmem : lv 1 γ 0 ∈ PK K := (pkLaws.2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by
    have h0 : nn (K := K) ((0 : unipLattice K (2 + 2) 2) : UPos (2 + 2) 2 → 𝔸[K]) = 1 := nn_zero
    rw [h0, one_mul]
    rfl⟩
  have e : lv m₂ (γ * m) s = lv 1 γ 0 * lv m₂ m s := by
    rw [blkLaws.2.1, one_mul, zero_add]
  rw [e, mul_assoc, hP.rat _ hmem]

private theorem rep_ae {K : Type} [Field K] [NumberField K] {μ : Measure (G1 K 2)} [μ.IsHaarMeasure] {v : L2 μ}
    {φ : G1 K 2 → ℂ} (hc : Continuous φ) (hi : ∀ γ ∈ Gam K 2, ∀ y, φ (γ * y) = φ y) (hr : Reps μ v φ) :
    (v : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ] fun y => φ (Quotient.out y) := by
  have h2 := IsContRep.ae_eq_quotFun (μ := μ) (φ := v) (F := φ) ⟨hc, hi, hr⟩
  refine h2.trans (Eventually.of_forall fun y => ?_)
  show quotFun φ hi y = φ (Quotient.out y)
  conv_lhs => rw [← Quotient.out_eq y]
  rfl

private theorem long_swap {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ) (m m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) (hF : Continuous F) :
    (∫ X, F (w0 K * nn X * (lv m m₂ s * k)) ∂unipMeasure K (2 + 2) 2) =
      (Real.exp (4 * s) : ℝ) • ∫ X, F (lv m₂ m (-s) * (w0 K * nn X * k)) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨e, he, hm⟩ := adMeas m m₂ s
  have h1 : ∀ X, F (w0 K * nn X * (lv m m₂ s * k)) = F (lv m₂ m (-s) * (w0 K * nn (e X) * k)) := fun X => by
    congr 1
    calc w0 K * nn X * (lv m m₂ s * k) = w0 K * (nn X * lv m m₂ s) * k := by simp only [mul_assoc]
      _ = w0 K * (lv m m₂ s * nn (e X)) * k := by rw [he]
      _ = (w0 K * lv m m₂ s) * nn (e X) * k := by simp only [mul_assoc]
      _ = lv m₂ m (-s) * w0 K * nn (e X) * k := by rw [blkLaws.2.2.2.2.2.2.2.2.2.1]
      _ = _ := by simp only [mul_assoc]
  simp_rw [h1]
  have hme : MeasurableEmbedding (e : (UPos (2 + 2) 2 → _) → _) := e.toHomeomorph.measurableEmbedding
  rw [← hme.integral_map (g := fun X => F (lv m₂ m (-s) * (w0 K * nn X * k))), hm, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

private theorem long_cont {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ} (hF : Continuous F) (m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) :
    Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => F (lv m₂ p.1 (-s) * (w0 K * nn p.2 * k)) := by
  have hl : Continuous fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2 := by
    obtain ⟨-, -, -, h, -⟩ := blkLaws (K := K)
    exact h
  have h0 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => ((m₂, p.1, -s) : G1 K 2 × G1 K 2 × ℝ) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_const)
  have h1 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => lv m₂ p.1 (-s) := by
    have h := Continuous.comp hl h0
    simpa only [Function.comp_def] using h
  have h2 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => nn p.2 :=
    (continuous_unipOne (K := K) (n := 2 + 2) 2).comp continuous_snd
  exact hF.comp (h1.mul ((continuous_const.mul h2).mul continuous_const))

private theorem swap_zero {Y X : Type} [MeasurableSpace Y] [MeasurableSpace X] (Q : Measure Y) (ν : Measure X)
    [IsFiniteMeasure Q] [IsFiniteMeasure ν] (f : Y → X → ℂ) (hI : Integrable (Function.uncurry f) (Q.prod ν))
    (hZ : ∀ x, ∫ y, f y x ∂Q = 0) : ∫ y, ∫ x, f y x ∂ν ∂Q = 0 := by
  rw [integral_integral_swap hI]
  simp only [hZ, integral_zero]

theorem UpperTheory.constantTerm_pairing_vanishes_of_orthogonal :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ ρ : Submodule ℂ (L2 μ₂)) (F : G1 K (2 + 2) → ℂ) (h : G1 K 2 → ℂ),
          PFun F → InBand F → Slices τ₁ τ₂ F → τ₂ ⟂ ρ → Continuous h → (∀ γ ∈ Gam K 2, ∀ m, h (γ * m) = h m) → (∃ v ∈ ρ, Reps μ₂ v h) →
          ∀ (m₂ : G1 K 2) (s : ℝ), ∀ k ∈ KG K (2 + 2),
            Integrable (fun y : RightCosetSpace (Gam K 2) => (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y))) (quotientMeasure (Gam K 2) μ₂) ∧
            ∫ y : RightCosetSpace (Gam K 2), (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) ∂quotientMeasure (Gam K 2) μ₂ = 0 := by
  intro K _ _ μ₂ _ τ₁ τ₂ ρ F h hP hB hS hort hc hi hv m₂ s k hk
  obtain ⟨v, hvρ, hvr⟩ := hv
  have hQf := isFiniteMeasure_quotientMeasure (K := K) (n := 2) μ₂
  obtain ⟨R, hR⟩ := hB
  obtain ⟨B, hBd⟩ := hP.bdd
  obtain ⟨C, hCc, hC⟩ := (longCell (K := K)).2 (R - s)
  haveI : IsFiniteMeasure ((unipMeasure K (2 + 2) 2).restrict C) := ⟨by simpa using hCc.measure_lt_top⟩
  let Φ : G1 K 2 → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun m X => F (lv m₂ m (-s) * (w0 K * nn X * k))
  let P : RightCosetSpace (Gam K 2) → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun y X => Φ (Quotient.out y) X
  let H : RightCosetSpace (Gam K 2) → ℂ := fun y => h (Quotient.out y)
  have hΦi : ∀ X, ∀ γ ∈ Gam K 2, ∀ m, Φ (γ * m) X = Φ m X := fun X γ hγ m => lv_left hP m₂ (-s) γ hγ m _
  have hΦc : Continuous (Function.uncurry Φ) := long_cont hP.cont m₂ s k
  have hPq : ∀ y X, P y X = quotFun (fun m => Φ m X) (hΦi X) y := fun y X => by
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have hPc : Continuous (Function.uncurry P) := by
    have hq := (isOpenQuotientMap_mk (Gam K 2)).prodMap (IsOpenQuotientMap.id (X := UPos (2 + 2) 2 → 𝔸[K]))
    rw [hq.isQuotientMap.continuous_iff]
    refine hΦc.congr fun p => ?_
    show Φ p.1 p.2 = P (mk (Gam K 2) p.1) p.2
    rw [hPq]
    rfl
  have hPb : ∀ y X, ‖P y X‖ ≤ B := fun y X => hBd _
  have hsupp : ∀ m X, X ∉ C → Φ m X = 0 := fun m X hX => by
    by_contra hne
    have h1 := hR _ hne
    have h2 := (hpSpec (K := K)).1 0 m₂ m (-s) (w0 K * nn X * k)
    rw [nn_zero, one_mul] at h2
    rw [h2, abs_le] at h1
    exact hX (hC X k hk (by linarith [h1.1]))
  have hHr := rep_ae hc hi hvr
  have hHm : MemLp H 2 (quotientMeasure (Gam K 2) μ₂) := (Lp.memLp v).ae_eq hHr
  have hHi : Integrable H (quotientMeasure (Gam K 2) μ₂) := hHm.integrable one_le_two
  have hHs : AEStronglyMeasurable H (quotientMeasure (Gam K 2) μ₂) := hHi.1
  have hI : Integrable (Function.uncurry fun y X => P y X * starRingEnd ℂ (H y))
      ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) := by
    have hm : AEStronglyMeasurable (fun p : RightCosetSpace (Gam K 2) × (UPos (2 + 2) 2 → 𝔸[K]) => starRingEnd ℂ (H p.1))
        ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) :=
      (continuous_star.comp_aestronglyMeasurable hHs).comp_fst
    refine Integrable.mono' (hHi.norm.mul_prod (integrable_const B))
      (hPc.aestronglyMeasurable.mul hm) (Eventually.of_forall fun p => ?_)
    show ‖P p.1 p.2 * starRingEnd ℂ (H p.1)‖ ≤ ‖H p.1‖ * B
    rw [norm_mul, RCLike.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_left (hPb _ _) (norm_nonneg _)
  have hT : ∀ y : RightCosetSpace (Gam K 2),
      (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) =
        (Real.exp (4 * s) : ℝ) • ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2 := fun y => by
    rw [long_swap F _ m₂ s k hP.cont, smul_mul_assoc, integral_mul_const]
    congr 2
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun X hX => hsupp _ X hX).symm
  have hZ : ∀ X, ∫ y, P y X * starRingEnd ℂ (H y) ∂quotientMeasure (Gam K 2) μ₂ = 0 := fun X => by
    obtain ⟨u, huτ, hur⟩ := (hS (lv 1 1 (-s) * (w0 K * nn X * k))).2 m₂
    have hur' : Reps μ₂ u (fun m => Φ m X) := by
      have e : (fun m => F (lv m₂ m 0 * (lv 1 1 (-s) * (w0 K * nn X * k)))) = fun m => Φ m X := by
        funext m
        show _ = F (lv m₂ m (-s) * (w0 K * nn X * k))
        rw [← mul_assoc, blkLaws.2.1, mul_one, mul_one, zero_add]
      rwa [e] at hur
    have h1 : (u : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ₂] fun y => P y X :=
      rep_ae (hΦc.comp (continuous_id.prodMk continuous_const)) (hΦi X) hur'
    have h3 : inner ℂ v u = 0 := inner_eq_zero_symm.1 (Submodule.isOrtho_iff_inner_eq.1 hort u huτ v hvρ)
    rw [L2.inner_def] at h3
    rw [← h3]
    refine integral_congr_ae ?_
    filter_upwards [h1, hHr] with y a b
    rw [a, b, RCLike.inner_apply]
  have hI2 : Integrable (fun y => ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2)
      (quotientMeasure (Gam K 2) μ₂) := hI.integral_prod_left
  refine ⟨?_, ?_⟩
  · simp_rw [hT]
    exact hI2.smul (Real.exp (4 * s))
  · simp_rw [hT]
    rw [integral_smul, @swap_zero _ _ _ _ _ _ hQf _ _ hI hZ, smul_zero]
