import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FiniteAdeleInclusionMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RayLv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndAmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.CoordMulInvCoordEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsLocalSubrepOfIsotypicTensorNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.XSimple

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.zSimple :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι → SimpleIn (rS ι) (Zs τ₁ τ₂ κ e (im w)) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA r w ι hw hι
  have hz := (zMem μ₂ τ₁ τ₂ κ e hA.idem).2 w ι hw hι
  refine ⟨fun g v hv => (hz v hv).2 g, fun Q hQ hst => ?_⟩
  obtain ⟨ι₂, hι₂⟩ := (embEx 2 w hw).1
  have hm := evMem μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι₂ ι hw hι₂ hι
  have hi := evInj μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA w ι hw hι
  have hc1 : CuspIrr μ₂ τ₁ := hP.1
  have hc2 : CuspIrr μ₂ τ₂ := hP.2
  by_cases hQ0 : Q = ⊥
  · exact Or.inl hQ0
  right
  obtain ⟨q, hq, hq0⟩ := (Submodule.ne_bot_iff _).1 hQ0
  have hX : tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) ≠ ⊥ := by
    intro h
    refine hq0 (hi q (hQ hq) ?_)
    funext g
    have := (hm q (hQ hq)).1.1 g
    rw [h] at this
    exact this
  have h12 := x12 μ₂ τ₁ τ₂ κ₂ p₁ p₂ hc1 hc2 hA.rank₁ hA.rank₂ w ι₂ hw hι₂
  have hS := indAmb (fun i => PW (w i)) (xS ι₂) _ h12.1 h12.2
    (exists_local_subrep_of_isotypic_tensor_ne_bot μ₂ τ₁ τ₂ κ₂ p₁ p₂ hc1 hc2 hA.rank₁.1 hA.rank₂.1 w ι₂ hw hι₂ hX)
  have hint : ∀ g φ, ev ι k₀ (rS ι g φ) = rightReg ℂ _ _ g (ev ι k₀ φ) := by
    intro g φ
    funext x m
    change φ (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι x) * fin1 (ι g)) = φ (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι (x * g)))
    simp only [fin1, map_mul, mul_assoc]
  rcases hS.2 (Q.map (ev ι k₀)) (by rintro _ ⟨φ, hφ, rfl⟩; exact hm φ (hQ hφ))
    (by rintro g _ ⟨φ, hφ, rfl⟩; exact ⟨_, hst g φ hφ, hint g φ⟩) with h | h
  · exact absurd (hi q (hQ hq) (by have := Submodule.mem_map_of_mem (f := ev ι k₀) hq; rw [h] at this; exact this)) hq0
  · refine le_antisymm hQ fun φ hφ => ?_
    have := hm φ hφ
    rw [← h] at this
    obtain ⟨ψ, hψ, e⟩ := this
    have : φ - ψ = 0 := hi _ (Submodule.sub_mem _ hφ (hQ hψ)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 this]; exact hψ
