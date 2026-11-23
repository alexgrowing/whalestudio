import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.BesselIntegralSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousLmulM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.MeasurableIndicatorNormSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem sInt_shift_eq_smul {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [CompleteSpace Vp] (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (f g : Mat k r → ℂ) (c₁ : ℂ)
    (hfg : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = c₁ * g y) (ξ : Vp) (x₀ x : Mat k r)
    (hx₀ : x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    sInt μW μN ψ π (fun y => f (x₀⁻¹ * y)) ξ x = c₁ • sInt μW μN ψ π (fun y => g (x₀⁻¹ * y)) ξ x := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  unfold sInt
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hfg _ (mul_mem_UH' (inv_mem_UH' hx₀) (mul_mem_UH' (mul_mem_UH' hp1.1 hp2.1) hx)), mul_smul]

theorem nvh_of_b_of (hE : SigZeroStatement) (hS : BesselIntegralSquareIntegrable) (hπ : HCTypeWURepStatement)
    (hO : HaarOpenPosStatement) (hIG : S0.IntGStatement) (hIS : S0.IntSStatement)
    (hHWN : HaarWNStatement) : NVHOfBStatement := by
  intro hB k r z c u v b h hset
  obtain ⟨H, i1, i2, i3, σ₀, hDS, hU, hw⟩ := hE k r z c u v b h hset
  refine ⟨H, i1, i2, i3, σ₀, hDS, ?_⟩
  intro w₀ hw₀ Vp _ _ _ π hπW μG μS ν hG hSm hQ
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  obtain ⟨hF, ⟨a, C, ha, hdec⟩, T, μ, P, v₁, c₁, hv₁, hc₁, hμ, hP, hcoef⟩ := hw w₀ hw₀
  obtain ⟨d, hd⟩ := hF μG hG
  have hz := hset.2.2.1
  have hT := hset.2.2.2.1
  have hc := hset.2.2.2.2.1
  obtain ⟨⟨μW, hμW⟩, ⟨μN, hμN⟩⟩ := hHWN k r z hz hT
  have hπU := hπ k r z u Vp π hz hT hπW
  have hBD : IsBData z c u π μW μN := ⟨hz, hT, hc, hπW, hμW, hμN⟩
  obtain ⟨ξ, x₀, x, hx₀, hx, hne⟩ := hB k r z c u v b h hset T μ P z c Vp π μW μN hμ hP hBD v₁ hv₁
  have hw1 : ‖w₀‖ = 1 := by
    obtain ⟨P', _, hl⟩ := hw₀
    exact hl.1
  obtain ⟨hcont, hequiv, hmG, hmν, hL2⟩ :=
    hS k r H σ₀ w₀ a C Vp π z c u μG μS ν μW μN hU hdec ha hBD hG hSm hQ x₀ hx₀ ξ
  refine ⟨_, hmG, hmν, hequiv, hL2, ?_, ?_⟩
  · refine S0.Fwd.nonzero k r z c Vp π μG μS ν _ (fun h' hh' v' => hπU.2.1 h' hh' v') hG hSm hQ
      (hO k r μG hG) hcont hequiv ⟨x, hx, ?_⟩
    rw [sInt_shift_eq_smul z μW μN hμW hμN _ π (fun y => ⟪w₀, σ₀ y w₀⟫_ℂ) (psiCoef T μ P v₁ v₁) c₁ hcoef ξ
      x₀ x hx₀ hx]
    exact smul_ne_zero hc₁ hne
  · intro y hy
    exact S0.Dec.repro_of_int hIG hIS k r H σ₀ w₀ d a C Vp π z c μG μW μN hU hw1 hd hdec ha hz hT hπU hG
      hμW hμN x₀ hx₀ ξ y hy

theorem haarOpenPos : HaarOpenPosStatement := by
  intro k r μG hG U hU hy
  obtain ⟨y, hyU, hyG⟩ := hy
  rw [pos_iff_ne_zero]
  intro h0
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), μG (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s ⁻¹' U) = 0 := by
    intro s hs
    rw [← Measure.map_apply (continuous_lmulM' s).measurable hU.measurableSet, hG.2.2.2 s hs, h0]
  let f : {s : Mat k r // s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} → Set (Formalism.QuantumDeterminants.Mt k r) :=
    fun s => Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s.1 ⁻¹' U
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable f
    (fun s => hU.preimage (continuous_lmulM' s.1))
  have hcov : {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} ⊆ ⋃ i ∈ T, f i := by
    intro x hx
    rw [hTeq, Set.mem_iUnion]
    have hx' : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hx
    refine ⟨⟨Matrix.of y * (Matrix.of x)⁻¹, mul_mem_UH' hyG (inv_mem_UH' hx')⟩, ?_⟩
    have e : Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of y * (Matrix.of x)⁻¹) x = y := by
      change (Matrix.of y * (Matrix.of x)⁻¹ * Matrix.of x : Mat k r) = Matrix.of y
      rw [Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hx', Matrix.mul_one]
    show Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of y * (Matrix.of x)⁻¹) x ∈ U
    rw [e]
    exact hyU
  have hA : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 :=
    measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun i _ => hinv i.1 i.2)
  have hAc : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := hG.2.2.1
  apply hG.2.1
  rw [← Measure.measure_univ_eq_zero]
  have hu : (Set.univ : Set (Formalism.QuantumDeterminants.Mt k r)) =
      {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} ∪ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    exact em _
  rw [hu]
  exact measure_union_null hA hAc

end ReciprocityTheory.ChartRestriction.DS.Lap
