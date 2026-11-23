import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Ext4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.UpdateMulSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ContinuousEntCSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpInjInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.MinSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.RankInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem idemTr (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι)
    (μ : Measure U4) (e : ι → U4 → ℂ) (hμ : Haar4 μ)
    (h : Idem (Measure.pi fun _ : ι => μ) fun k => ∏ i, e i (k i)) : IdemA (C.κ₄ μ) (C.e e) := by
  refine ⟨(coLaws K ι C).2.1 μ hμ, h.cont.comp (C.Φ (2 + 2)).continuous, fun k => ?_, fun k => ?_⟩
  · have := h.star (C.Φ (2 + 2) k)
    rw [← map_inv] at this
    exact this
  · have := h.idem (C.Φ (2 + 2) k)
    have hm := integral_map_equiv (μ := Measure.pi fun _ : ι => μ) (C.Φ (2 + 2)).symm.toHomeomorph.toMeasurableEquiv
      (fun h => C.e e h * C.e e (h⁻¹ * k))
    refine Eq.trans hm (Eq.trans ?_ this)
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    change C.e e ((C.Φ (2 + 2)).symm a) * C.e e (((C.Φ (2 + 2)).symm a)⁻¹ * k) = _
    simp only [Co.e, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.archEx :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.ArchEx := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ τ₁ τ₂ θ hP hθ h12 h21 D
  obtain ⟨CF, CE, hC⟩ := coEx F E σ D
  obtain ⟨μ, hμ, hpos⟩ := u4.2.2.2.2.2.2.2.2.2.2.2.2
  have c₁ : CuspIrr (BW.mu1 E 2) τ₁ := hP.1
  have c₂ : CuspIrr (BW.mu1 E 2) τ₂ := hP.2
  choose n q hn using fun u : InfinitePlace F => minEx E _ CE _ τ₁ c₁ (0, u)
  choose n' q' hn' using fun u : InfinitePlace F => minEx E _ CE _ τ₂ c₂ (0, u)
  choose e4 he he' using fun u : InfinitePlace F => ext4 μ hμ hpos (n u) (q u) (n' u) (q' u)
  let N : Fin 2 × InfinitePlace F → ℕ := fun i => ![n i.2, n' i.2] i.1
  let Q : Fin 2 × InfinitePlace F → ℤ := fun i => ![q i.2, q' i.2] i.1
  let N' : Fin 2 × InfinitePlace F → ℕ := fun i => ![n' i.2, n i.2] i.1
  let Q' : Fin 2 × InfinitePlace F → ℤ := fun i => ![q' i.2, q i.2] i.1
  let x : Fin 2 × InfinitePlace F → U4 := fun i => ![1, w4] i.1
  have hE : ExtP μ (fun i : Fin 2 × InfinitePlace F => e4 i.2) N Q N' Q' x := by
    refine extPi _ μ _ N Q N' Q' x hμ ?_
    rintro ⟨s, u⟩
    fin_cases s
    · exact he u
    · exact he' u
  have hF : ExtP μ e4 n q n' q' (fun _ => 1) := extPi _ μ _ n q n' q' _ hμ he
  have m₁ : ∀ i, CE.MinAt (BW.mu1 E 2) τ₁ i (N i) (Q i) := by
    rintro ⟨s, u⟩
    fin_cases s
    · exact hn u
    · exact minSwap F E σ D CF CE hC _ θ hθ τ₂ τ₁ h21 0 u _ _ (hn' u)
  have m₂ : ∀ i, CE.MinAt (BW.mu1 E 2) τ₂ i (N' i) (Q' i) := by
    rintro ⟨s, u⟩
    fin_cases s
    · exact hn' u
    · exact minSwap F E σ D CF CE hC _ θ hθ τ₁ τ₂ h12 0 u _ _ (hn u)
  have hv := lineVal E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE
  refine ⟨CF.κ₄ μ, CF.e e4, CE.κ₄ μ, CE.e (fun i => e4 i.2), CE.κ₂, CE.p N Q, CE.p N' Q', (CE.Φ (2 + 2)).symm x,
    idemTr F _ CF μ e4 hμ hF.idem, ?_, hv.1, rankInf E _ CE _ τ₁ c₁ N Q fun i => (m₁ i).1,
    rankInf E _ CE _ τ₂ c₂ N' Q' fun i => (m₂ i).1, hv.2,
    lineInj E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE m₁ m₂,
    lineEx E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE (fun i => (m₁ i).1) fun i => (m₂ i).1⟩
  intro k kk hk
  simp only [Co.e]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun u _ => ?_
  congr 1
  apply Subtype.ext
  rw [CE.Φ_val, CF.Φ_val, hC, hk]
