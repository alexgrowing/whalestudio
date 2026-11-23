import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ContLv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ext_two {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T T' : E →L[ℂ] H) (S S' : F →L[ℂ] H) (a : Set E) (b : Set F)
    (h : ∀ u ∈ a, ∀ v ∈ b, ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ) :
    ∀ u ∈ closure (Submodule.span ℂ a : Set E), ∀ v ∈ closure (Submodule.span ℂ b : Set F),
      ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ := by
  have h1 : ∀ u ∈ a, ∀ v ∈ closure (Submodule.span ℂ b : Set F), ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ := by
    intro u hu v hv
    have hc : IsClosed {v : F | ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ} := isClosed_eq (by fun_prop) (by fun_prop)
    refine hc.closure_subset_iff.2 (fun w hw => ?_) hv
    induction hw using Submodule.span_induction with
    | mem x hx => exact h u hu x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [mem_setOf_eq] at hx hy ⊢
      rw [map_add, map_add, inner_add_right, inner_add_right, hx, hy]
    | smul c x _ hx =>
      simp only [mem_setOf_eq] at hx ⊢
      rw [map_smul, map_smul, inner_smul_right, inner_smul_right, hx]
  intro u hu v hv
  have hc : IsClosed {u : E | ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ} := isClosed_eq (by fun_prop) (by fun_prop)
  refine hc.closure_subset_iff.2 (fun w hw => ?_) hu
  induction hw using Submodule.span_induction with
  | mem x hx => exact h1 x hx v hv
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_add, inner_add_left, inner_add_left, hx, hy]
  | smul c x _ hx =>
    simp only [mem_setOf_eq] at hx ⊢
    rw [map_smul, map_smul, inner_smul_left, inner_smul_left, hx]

private theorem pure_pair {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    (D : TypeDat K (2 + 2)) (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') :
    ∃ (c : ℝ) (κ : Measure (KG K (2 + 2))), ∀ (β β' : ℝ → ℂ) (e : Eu d) (e' : Eu d') (u : L (Eu d)) (v : L (Eu d')),
      Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' → (∀ᵐ x : ℝ, u x = β x • e) →
      (∀ᵐ x : ℝ, v x = β' x • e') → ⟪A.J u, A'.J v⟫_ℂ = c * ∫ t : ℝ, ∫ k : KG K (2 + 2), ∫ X,
        conj (β t) * β' (HH (w0 K * nn X * k.1) - t) * Complex.exp (2 * (HH (w0 K * nn X * k.1) : ℂ)) *
          pw μ₂ (A.sec e) (A'.sec e') k (w0 K * nn X * k.1) ∂unipMeasure K (2 + 2) 2 ∂κ := by
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace (KG K (2 + 2)) := hK.isClosed.locallyCompactSpace
  obtain ⟨c, hc⟩ := (unf μ μ₂ (Measure.haar : Measure (KG K (2 + 2)))).1
  refine ⟨c, Measure.haar, fun β β' e e' u v hβ hβc hβ' hβc' hu hv => ?_⟩
  obtain ⟨hs, hf⟩ := (A.onto (A.sec e)).1 ⟨e, rfl⟩
  obtain ⟨hs', hf'⟩ := (A'.onto (A'.sec e')).1 ⟨e', rfl⟩
  have hS := secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hs hf
  have hS' := secFun μ₂ τ₂ τ₁ D hP.irr₂ hP.irr₁ _ hs' hf'
  have hl := ((secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hf).1 hs).2.2.2.2
  have hl' := ((secCrit μ₂ τ₂ τ₁ D hP.irr₂ hP.irr₁ _ hf').1 hs').2.2.2.2
  have h0 : ∀ x y, pm μ₂ (A.sec e) (A'.sec e') x y = 0 := fun x y =>
    ((pmLaws μ₂ (Measure.haar : Measure (KG K (2 + 2)))).1 τ₁ τ₂ τ₂ τ₁ _ _ hS hS' hl hl' x y).1 hP.orth
  rw [pairF μ μ₂ Measure.haar c hc _ _ β β' hS hS' hβ hβc hβ' hβc' _ _ (A.spec β e u hβ hβc hu)
    (A'.spec β' e' v hβ' hβc' hv)]
  simp only [h0, integral_zero, mul_zero, zero_add]

private theorem sh_pure {d : ℕ} (s : ℝ) (β : ℝ → ℂ) (e : Eu d) (u : L (Eu d)) (hu : ∀ᵐ x : ℝ, u x = β x • e) :
    ∀ᵐ x : ℝ, UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s u x = β (x + s) • e := by
  filter_upwards [UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d) s u,
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae hu] with x h1 h2
  rw [h1, h2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pairFacts :
    UnipotentBlockPairs := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨c, κ, hpure⟩ := pure_pair μ μ₂ τ₁ τ₂ hP D d d' A A'
  refine ⟨fun s u u' v v' hu hv => ?_, fun s u v hu hv => ?_⟩
  · have e1 : u' = UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s u := Lp.ext (by
      filter_upwards [hu, UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d) s u] with x h1 h2
      rw [h1, h2])
    have e2 : v' = UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d') s v := Lp.ext (by
      filter_upwards [hv, UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d') s v] with x h1 h2
      rw [h1, h2])
    subst e1 e2
    refine ext_two (A.J.toContinuousLinearMap ∘L UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s) A.J.toContinuousLinearMap
      A'.J.toContinuousLinearMap (A'.J.toContinuousLinearMap ∘L UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d') s) _ _ ?_
      u ((denseCc d).1 u) v ((denseCc d').1 v)
    rintro p ⟨β, e, hβ, hβc, hp⟩ q ⟨β', e', hβ', hβc', hq⟩
    have a1 := hpure (fun x => β (x + s)) β' e e' _ q (by fun_prop)
      (hβc.comp_homeomorph (Homeomorph.addRight s)) hβ' hβc' (sh_pure s β e p hp) hq
    have a2 := hpure β (fun x => β' (x + s)) e e' p _ hβ hβc (by fun_prop)
      (hβc'.comp_homeomorph (Homeomorph.addRight s)) hp (sh_pure s β' e' q hq)
    refine a1.trans (Eq.trans ?_ a2.symm)
    congr 1
    refine Eq.trans ?_ (integral_add_right_eq_self _ s)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : ∀ h : ℝ, h - (t + s) + s = h - t := fun h => by ring
    simp only [this]
  · have := ext_two A.J.toContinuousLinearMap 0 A'.J.toContinuousLinearMap 0 _ _ ?_
      u ((denseCc d).2.2 s u hu) v ((denseCc d').2.2 (2 * 0 - s) v hv)
    · simpa using this
    rintro p ⟨β, e, hβ, hβc, hz, hp⟩ q ⟨β', e', hβ', hβc', hz', hq⟩
    have a1 := hpure β β' e e' p q hβ hβc hβ' hβc' hp hq
    refine a1.trans ?_
    have h0 : ∀ (t : ℝ) (k : KG K (2 + 2)) (X : UPos (2 + 2) 2 → 𝔸[K]),
        conj (β t) * β' (HH (w0 K * nn X * k.1) - t) = 0 := by
      intro t k X
      rcases le_or_gt t s with h | h
      · rw [hz t h, map_zero, zero_mul]
      · have := (longCell (K := K)).1 X k.1 k.2
        rw [hz' _ (by linarith), mul_zero]
    simp only [h0, zero_mul, integral_zero, mul_zero, ContinuousLinearMap.zero_apply, inner_zero_left]
