import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem int_map {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (n : ℕ)
    [MeasurableSpace (unitaryGroup (Fin n) ℂ)] [BorelSpace (unitaryGroup (Fin n) ℂ)]
    (ν : Measure (ι → unitaryGroup (Fin n) ℂ)) (F : archCompact K n → ℂ) :
    ∫ k, F k ∂(Measure.map (C.Φ n).symm ν) = ∫ y, F ((C.Φ n).symm y) ∂ν :=
  ((C.Φ n).symm.toHomeomorph.measurableEmbedding).integral_map F

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineVal :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      IdemA (C.κ₄ μ) (C.e e) ∧ ∀ f, IsSec τ₁ τ₂ f → FixA (C.κ₄ μ) (C.e e) f → ∀ h : FA K (2 + 2),
        (∀ m₂, FixA C.κ₂ (C.p n q) fun m₁ => f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h)) ∧
        ∀ m₁, FixA C.κ₂ (C.p n' q') fun m₂ => f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ _ μ e n q n' q' x h4 hE
  obtain ⟨hκ₂, hκ₄, -, -, -, -, -, -, -, hlv, hcomm, -⟩ := coLaws K ι C
  have hb := blkLaws (K := K)
  have hmul := hb.2.1
  have he : ∀ k, C.e e ((C.Φ (2 + 2)).symm k) = ∏ i, e i (k i) := by
    intro k; simp only [Co.e, ContinuousMulEquiv.apply_symm_apply]
  have hp : ∀ (a : ι → ℕ) (b : ι → ℤ) k, C.p a b ((C.Φ 2).symm k) = ∏ i, T (a i) (b i) (k i) := by
    intro a b k; simp only [Co.p, ContinuousMulEquiv.apply_symm_apply]
  have ha : ∀ a b : ι → U4, arc1 ((C.Φ (2 + 2)).symm (a * b)) =
      arc1 ((C.Φ (2 + 2)).symm a) * arc1 ((C.Φ (2 + 2)).symm b) := by
    intro a b; simp [arc1, map_mul]
  have h1 : (arc1 ((C.Φ 2).symm (1 : ι → U2)) : G1 K 2) = 1 := by simp [arc1, map_one]
  refine ⟨⟨hκ₄ μ h4, ?_, ?_, ?_⟩, ?_⟩
  · exact hE.idem.cont.comp (C.Φ (2 + 2)).continuous
  · intro k
    have := hE.idem.star (C.Φ (2 + 2) k)
    simp only [Co.e, map_inv]
    exact this
  · intro k
    have := hE.idem.idem (C.Φ (2 + 2) k)
    rw [Co.κ₄, int_map]
    simp only [Co.e, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    exact this
  · intro f hf hfix h
    have hc : ∀ L : G1 K (2 + 2), Continuous fun k : ι → U4 => f (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro L
      refine hf.cont.comp (continuous_const.mul ?_)
      exact continuous_archP.comp (continuous_subtype_val.comp (C.Φ (2 + 2)).symm.continuous)
    have hr : ∀ L : G1 K (2 + 2), RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i))
        fun k : ι → U4 => f (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro L g
      have := hfix (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm g))
      rw [Co.κ₄, int_map] at this
      simp only [he] at this
      simp only [ha, ← mul_assoc]
      exact this
    refine ⟨fun m₂ g => ?_, fun m₁ g => ?_⟩
    · have := (hE.fix _ (hc (lv g m₂ 0)) (hr (lv g m₂ 0)) 1).1
      simp only [one_mul] at this
      change ∫ k, C.p n q k * f (lv (g * arc1 k) m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) ∂C.κ₂ = _
      rw [Co.κ₂, int_map]
      simp only [hp]
      have e1 : ∀ m : ι → U2, lv (g * arc1 ((C.Φ 2).symm m)) m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h =
          lv g m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd (m i) 1) * x)) := by
        intro m
        have hl := hlv m 1
        rw [h1] at hl
        have h2 : lv (g * arc1 ((C.Φ 2).symm m)) m₂ 0 =
            lv g m₂ 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd (m i) 1) := by
          have := hmul g m₂ (arc1 ((C.Φ 2).symm m)) 1 0 0
          rw [hl, mul_one, add_zero] at this
          exact this.symm
        rw [h2, ha, mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), ← ha,
          (hcomm _ _ h).eq]
      simp only [e1]
      rw [this, mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), (hcomm _ _ h).eq]
    · have := (hE.fix _ (hc (lv m₁ g 0)) (hr (lv m₁ g 0)) 1).2
      simp only [one_mul] at this
      change ∫ k, C.p n' q' k * f (lv m₁ (g * arc1 k) 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) ∂C.κ₂ = _
      rw [Co.κ₂, int_map]
      simp only [hp]
      have e1 : ∀ m : ι → U2, lv m₁ (g * arc1 ((C.Φ 2).symm m)) 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h =
          lv m₁ g 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd 1 (m i)) * x)) := by
        intro m
        have hl := hlv 1 m
        rw [h1] at hl
        have h2 : lv m₁ (g * arc1 ((C.Φ 2).symm m)) 0 =
            lv m₁ g 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd 1 (m i)) := by
          have := hmul m₁ g 1 (arc1 ((C.Φ 2).symm m)) 0 0
          rw [hl, mul_one, add_zero] at this
          exact this.symm
        rw [h2, ha, mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), ← ha,
          (hcomm _ _ h).eq]
      simp only [e1]
      rw [this, mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), (hcomm _ _ h).eq]
