import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecomposition
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.F.SelfK

open GlobalTheory.CompanionTheory.WaveMult.KerAdj

theorem self_adj (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hS : WaveSpeed) (hE : WaveEx) (hQ : KerUniq) (n : ℕ)
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (g : ℝ → ℝ) (T : ℝ)
    (k : Mat n → (E.V →L[ℂ] E.V)) (hb : IsBump g T) (hk : IsKer μ E [] g k) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = k y := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨c, hc⟩ : ∃ c : Fin 1 → ℂ, c = fun _ => 1 := ⟨_, rfl⟩
  obtain ⟨K, hKk⟩ : ∃ K : Fin 1 → Mat n → (E.V →L[ℂ] E.V), K = fun _ => k := ⟨_, rfl⟩
  have hK : ∀ i : Fin 1, IsKer μ E ((fun _ => []) i) g (K i) := fun i => by rw [hKk]; exact hk
  have hw : ∀ a b : Mat n → E.V, ContDiffOn ℝ ∞ a (GLs n) → ContDiffOn ℝ ∞ b (GLs n) → Cpt a → Cpt b →
      ∫ y : G n, ⟪zOp [] a y.val, b y.val⟫_ℂ ∂μ =
        ∑ i : Fin 1, c i * ∫ y : G n, ⟪a y.val, zOp ((fun _ => []) i) b y.val⟫_ℂ ∂μ := by
    intro a b _ _ _ _
    simp [hc, zOp]
  obtain ⟨regp, eqvp⟩ := GlobalTheory.T.kernel_adjoint_regular hL n E k ⟨hk.1.continuousOn, hk.2.1⟩ hk.2.2.1
  have regK : ∀ i, KReg (K i) := fun i => ⟨(hK i).1.continuousOn, (hK i).2.1⟩
  have rp : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (y * k₂.1)⁻¹) = ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂ := by
    intro y hy k₂
    simpa using eqvp y hy 1 k₂
  have lp : ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (k₁.1 * y)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) := by
    intro y hy k₁
    simpa using eqvp y hy k₁ 1
  have rK : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K i (y * k₂.1) = K i y * E.ρ k₂ := by
    intro i y hy k₂
    simpa using (hK i).2.2.1 y hy 1 k₂
  have lK : ∀ i, ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, K i (k₁.1 * y) = E.ρ k₁ * K i y := by
    intro i y hy k₁
    simpa using (hK i).2.2.1 y hy k₁ 1
  have hD : ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y = 0 := by
    refine hQ n μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) (GLs n)
      (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) subset_rfl
      (fun y hy k₂ => GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)) ?_ ?_ ?_
    · exact regp.1.sub (continuousOn_finset_sum _ fun i _ => (regK i).1.const_smul (c i))
    · intro y hy k₂
      simp only [rp y hy k₂, rK _ y hy k₂, sub_mul, Finset.sum_mul, smul_mul_assoc]
    · intro f hf cf _
      have hfc := hf.1.continuousOn
      have ap := GlobalTheory.T.kernel_action_equivariant hL n μ E _ f regp hfc lp
      have aK := fun i => GlobalTheory.T.kernel_action_equivariant hL n μ E (K i) f (regK i) hfc (lK i)
      have hA0 := section_orth_cpt_zero hQ n μ E
        (fun x => act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x - ∑ i, c i • act μ E (K i) f x)
        (ap.1.sub (continuousOn_finset_sum _ fun i _ => (aK i).1.const_smul (c i)))
        (by
          intro y hy k₂
          simp only [ap.2 y hy k₂, (aK _).2 y hy k₂, map_sub, map_sum, map_smul])
        (by
          intro h hh ch
          have int1 := pair_integrable μ hL ap.1 hh.1.continuousOn ch
          have int2 := fun i => (pair_integrable μ hL (aK i).1 hh.1.continuousOn ch).const_mul (conj (c i))
          have hpt : ∀ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val - ∑ i, c i • act μ E (K i) f y.val, h y.val⟫_ℂ
              = ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ
                - ∑ i, conj (c i) * ⟪act μ E (K i) f y.val, h y.val⟫_ℂ := by
            intro y
            simp only [inner_sub_left, sum_inner, inner_smul_left]
          simp only [hpt]
          rw [integral_sub int1 (integrable_finset_sum _ fun i _ => int2 i),
            integral_finset_sum _ fun i _ => int2 i]
          simp only [integral_const_mul]
          rw [chain μ hL hU hR hS hE hb hk hw hK hf cf hh ch, sub_self])
      have h1 := hA0 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      have h2 := act_eq_sum_of_kernel hL n μ E (ι := Option (Fin 1))
        (fun o => o.elim 1 fun i => -c i)
        (fun o => o.elim (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) K)
        (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) f
        (by rintro (_ | i); exacts [regp, regK i])
        (by intro y _; simp [Fintype.sum_option, sub_eq_add_neg])
        hfc 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      rw [h2]
      simpa [Fintype.sum_option, sub_eq_add_neg] using h1
  intro y hy
  simpa [hc, hKk] using sub_eq_zero.1 (hD y hy)

end PositivityTheory.Rg.BcB.F.SelfK

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG

theorem adjKer₀ : AdjKer0 := by
  intro n μ hμ M g T k hb hk
  haveI : BorelSpace (G n) := ⟨rfl⟩
  haveI := FiniteDimensional.complete ℂ M.V
  have h := SelfK.self_adj GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular GlobalTheory.T.right_derivative_calculus_holds wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.1 GlobalTheory.T.wave_kernel_uniqueness n μ M g T k hb hk
  refine ⟨hk.1.congr h, ?_, fun y hy k₁ k₂ => ?_, fun u hu x hx => ?_⟩
  · obtain ⟨R, hR⟩ := hk.2.1
    exact ⟨R, fun y hy hl => (h y hy).trans (hR y hy hl)⟩
  · have hm := GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₁) hy)
      (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)
    show ContinuousLinearMap.adjoint (k _⁻¹) = _ * ContinuousLinearMap.adjoint (k y⁻¹) * _
    rw [h _ hm, h y hy]
    exact hk.2.2.1 y hy k₁ k₂
  · rw [← hk.2.2.2 u hu x hx]
    simp only [act]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [h _ (PairAdj.val_mem_GLs z)]

end PositivityTheory.Rg.BcB.F
