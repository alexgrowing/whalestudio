import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterFunEqOfMapLeftMul
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_semidirect :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ N M _ _ _ hN hM hgen hdisj νN νM hNH hNR hMH hMR δ hδN hδM q
  haveI := hNH
  haveI := hNR
  haveI := hMH
  haveI := hMR
  haveI : BorelSpace N := Subtype.borelSpace (N : Set Q)
  haveI : BorelSpace M := Subtype.borelSpace (M : Set Q)
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement Q N M hN hM hgen hdisj
  let Ψ : (M × N) ≃ₜ Q := (Homeomorph.prodComm M N).trans Φ
  have hΨ : ∀ p : M × N, Ψ p = (p.2 : Q) * (p.1 : Q) := fun p => hΦ (p.2, p.1)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  set ρ : Measure Q := (νM.prod νN).map Ψ with hρ
  have hconj : ∀ (m : Q) (n : N), ((MulAut.conjNormal m n : N) : Q) = m * n * m⁻¹ :=
    fun m n => MulAut.conjNormal_apply m n
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) K = (νM.prod νN) (Ψ ⁻¹' K) from
      Ψ.toMeasurableEquiv.map_apply K]
    have : IsCompact (Ψ ⁻¹' K) := by
      have := hK.image Ψ.symm.continuous
      rwa [Ψ.symm.image_eq_preimage_symm, Ψ.symm_symm] at this
    exact this.measure_lt_top
  haveI : ρ.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) U = (νM.prod νN) (Ψ ⁻¹' U) from
      Ψ.toMeasurableEquiv.map_apply U]
    exact (hU.preimage Ψ.continuous).measure_ne_zero _ (hne.preimage Ψ.surjective)
  haveI : ρ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective g
    have hmul : Measurable (fun y : Q => y * Ψ (m₀, n₀)) := measurable_mul_const _
    have hc : Continuous (fun p : M × N => (MulAut.conjNormal (p.1 : Q) n₀ : N)) := by
      have h : Continuous (fun p : M × N => (p.1 : Q) * n₀ * (p.1 : Q)⁻¹) := by fun_prop
      exact Topology.IsInducing.subtypeVal.continuous_iff.2
        (h.congr fun p => (hconj _ _).symm)
    let T : M × N → M × N := fun p => (p.1 * m₀, p.2 * MulAut.conjNormal (p.1 : Q) n₀)
    have hT : MeasurePreserving T (νM.prod νN) (νM.prod νN) := by
      refine MeasurePreserving.skew_product (f := fun m : M => m * m₀)
        (g := fun (m : M) (n : N) => n * MulAut.conjNormal (m : Q) n₀)
        (measurePreserving_mul_right νM m₀) ?_ (Filter.Eventually.of_forall fun m => ?_)
      · exact (continuous_snd.mul hc).measurable
      · exact (measurePreserving_mul_right νN _).map_eq
    have hcomp : (fun y : Q => y * Ψ (m₀, n₀)) ∘ Ψ = Ψ ∘ T := by
      funext ⟨m, n⟩
      simp only [Function.comp, T, hΨ, Subgroup.coe_mul, hconj]
      group
    rw [hρ, Measure.map_map hmul hΨm, hcomp, ← Measure.map_map hΨm hT.measurable, hT.map_eq]
  refine GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_eq_of_map_left_mul Q ρ δ ?_ q
  intro q₀
  obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective q₀
  have hmul : Measurable (fun y : Q => Ψ (m₀, n₀) * y) := measurable_const_mul _
  have hcm : Continuous (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := by
    have h : Continuous (fun n : N => (m₀ : Q) * n * (m₀ : Q)⁻¹) := by fun_prop
    exact Topology.IsInducing.subtypeVal.continuous_iff.2
      (h.congr fun p => (hconj _ _).symm)
  let f₁ : M → M := fun m => m₀ * m
  let f₂ : N → N := fun n => n₀ * MulAut.conjNormal (m₀ : Q) n
  have hf₁ : Measurable f₁ := measurable_const_mul _
  have hf₂ : Measurable f₂ := (continuous_const.mul hcm).measurable
  have hcomp : (fun y : Q => Ψ (m₀, n₀) * y) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext ⟨m, n⟩
    simp only [Function.comp, Prod.map, f₁, f₂, hΨ, Subgroup.coe_mul, hconj]
    group
  have hνM : νM.map f₁ = νM := (measurePreserving_mul_left νM m₀).map_eq
  have hνN : νN.map f₂ = (δ m₀)⁻¹ • νN := by
    have : f₂ = (fun n : N => n₀ * n) ∘ (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hcm.measurable, hδM _ m₀.2,
      Measure.map_smul, (measurePreserving_mul_left νN n₀).map_eq]
  have hδ : δ (Ψ (m₀, n₀)) = δ m₀ := by
    rw [hΨ]
    simp [map_mul, hδN _ n₀.2]
  rw [hρ, Measure.map_map hmul hΨm, hcomp,
    ← Measure.map_map hΨm (hf₁.prodMap hf₂), ← Measure.map_prod_map νM νN hf₁ hf₂, hνM, hνN,
    Measure.prod_smul_right, Measure.map_smul, hδ]

end GlobalTheory.CompanionTheory.ModChar
