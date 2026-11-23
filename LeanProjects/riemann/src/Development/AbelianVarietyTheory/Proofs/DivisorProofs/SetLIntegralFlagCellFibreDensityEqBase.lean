import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingCurry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPtSplit
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem aemeasurable_fibDens {ι : Type} [Fintype ι] {m : ι → ℕ} {d : ℕ} (G : V d → Mat m ℂ) (O : Set (V d))
    (hO : IsOpen O) (hG : ∀ τ i j, ContinuousOn (fun v => G v τ i j) O) :
    AEMeasurable (fun x : V d × (Cell m → ℂ) => fibDens (G x.1) x.2)
      (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hGτ : ∀ τ, ContinuousOn (fun x : V d × (Cell m → ℂ) => G x.1 τ) (O ×ˢ Set.univ) := by
    intro τ
    have h : ContinuousOn (fun v => G v τ) O :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hG τ i j
    exact h.comp continuous_fst.continuousOn fun x hx => hx.1
  unfold fibDens
  apply Finset.aemeasurable_fun_prod
  intro τ _
  refine AEMeasurable.mul (AEMeasurable.mul aemeasurable_const ?_) ?_
  · have h := ((continuous_id.matrix_det).comp_continuousOn (hGτ τ))
    exact ((Complex.continuous_re.comp_continuousOn h).aemeasurable hS).pow_const _
  · unfold GlobalTheory.FlagFibre.dens
    apply Finset.aemeasurable_fun_prod
    intro i _
    refine AEMeasurable.pow_const (AEMeasurable.norm ?_) _
    have hc : Continuous fun p : Matrix (Fin (m τ)) (Fin (m τ)) ℂ × (Low (m τ) → ℂ) =>
        ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni p.2)ᴴ * p.1ᵀ * GlobalTheory.FlagFibre.uni p.2) i.castSucc := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      exact ((((GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd).matrix_conjTranspose.matrix_mul
        continuous_fst.matrix_transpose).matrix_mul (GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd)).matrix_submatrix
        _ _).matrix_det
    have h2 : ContinuousOn (fun x : V d × (Cell m → ℂ) => (G x.1 τ, fun s => x.2 ⟨τ, s⟩)) (O ×ˢ Set.univ) :=
      (hGτ τ).prodMk (by fun_prop : Continuous fun x : V d × (Cell m → ℂ) => fun s => x.2 ⟨τ, s⟩).continuousOn
    exact (hc.comp_continuousOn h2).aemeasurable hS

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem setLIntegral_fibDens : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  intro ι _ m n d ε G δ O K hO hK hKO hδ hG hpos
  have hmp := (GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).1
  have hb : Measurable (bsL ε) := (bsL ε).continuous.measurable
  have hm := hmp.restrict_preimage (hb hK)
  have hs : (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ⁻¹' (bsL ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [bsL_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  set F : V d × (Cell m → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (δ x.1 * fibDens (G x.1) x.2) with hF
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hFO : AEMeasurable F (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable (AEMeasurable.mul ?_ (aemeasurable_fibDens G O hO hG))
    exact (hδ.comp continuous_fst.continuousOn fun x hx => hx.1).aemeasurable hS
  have hFK : AEMeasurable F ((volume.restrict K).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Cell m → ℂ))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hFO.mono_measure (Measure.restrict_mono (Set.prod_mono hKO subset_rfl) le_rfl)
  have e1 : (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w))) ∘
      (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) = F := by
    funext x
    simp [hF, bsL_pt, fb_pt]
  have hH : AEMeasurable (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)))
      (Measure.map (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ((volume.restrict K).prod volume)) := by
    rw [(GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).2.aemeasurable_map_iff, e1]
    exact hFK
  rw [← hm.map_eq, lintegral_map' hH hm.measurable.aemeasurable]
  refine (lintegral_congr fun a => congrFun e1 a).trans ?_
  rw [lintegral_prod _ hFK]
  refine setLIntegral_congr_fun hK fun v hv => ?_
  obtain ⟨h0, h1⟩ := GlobalTheory.FlagCell2.fibDens_mass ι m (G v) (hpos v (hKO hv))
  simp only [hF]
  simp_rw [ENNReal.ofReal_mul' (h0 _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, mul_one]

end GlobalTheory.FlagCell2
