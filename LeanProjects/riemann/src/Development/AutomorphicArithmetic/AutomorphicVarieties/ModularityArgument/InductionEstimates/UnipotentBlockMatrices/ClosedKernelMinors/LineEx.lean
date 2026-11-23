import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IsoExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ContLv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.RepZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem frame_ex {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (B : V → V → ℂ)
    (hlin : ∀ f ∈ S, ∀ f' ∈ S, ∀ f'' ∈ S, ∀ a : ℂ, B f (a • f' + f'') = a * B f f' + B f f'')
    (hsym : ∀ f ∈ S, ∀ f' ∈ S, conj (B f f') = B f' f)
    (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (B f f).re) :
    ∃ (d : ℕ) (sec : Eu d →ₗ[ℂ] V), Function.Injective sec ∧ LinearMap.range sec = S ∧
      ∀ v v', B (sec v) (sec v') = ⟪v, v'⟫_ℂ := by
  have h0 : ∀ f ∈ S, B f 0 = 0 := by
    intro f hf
    have h := hlin f hf 0 S.zero_mem 0 S.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at h
    simpa using h
  let core : InnerProductSpace.Core ℂ S :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => hsym _ y.2 _ x.2
      re_inner_nonneg := fun x => by
        by_cases hx : (x : V) = 0
        · show 0 ≤ (B x x).re
          have : B x x = 0 := by
            have := h0 _ x.2
            rw [← hx] at this
            simpa [hx] using this
          simp [this]
        · exact (hpos _ x.2 hx).le
      add_left := fun x y z => by
        show B ((x : V) + y) z = B x z + B y z
        have h := hlin _ z.2 _ x.2 _ y.2 1
        rw [one_smul, one_mul] at h
        rw [← hsym _ z.2 _ (S.add_mem x.2 y.2), h, map_add, hsym _ z.2 _ x.2, hsym _ z.2 _ y.2]
      smul_left := fun x y r => by
        show B (r • (x : V)) y = conj r * B x y
        have h := hlin _ y.2 _ x.2 _ S.zero_mem r
        rw [add_zero, h0 _ y.2, add_zero] at h
        rw [← hsym _ y.2 _ (S.smul_mem r x.2), h, map_mul, hsym _ y.2 _ x.2]
      definite := fun x hx => by
        by_contra hne
        have h := hpos _ x.2 (fun h => hne (Subtype.ext h))
        have hx' : B x x = 0 := hx
        rw [hx'] at h
        simp at h }
  letI : NormedAddCommGroup S := @InnerProductSpace.Core.toNormedAddCommGroup ℂ S _ _ _ core
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore core.toCore
  let e := (stdOrthonormalBasis ℂ S).repr.symm
  refine ⟨Module.finrank ℂ S, S.subtype ∘ₗ (e.toLinearEquiv : _ →ₗ[ℂ] S), ?_, ?_, ?_⟩
  · exact S.injective_subtype.comp e.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  · intro v v'
    exact e.inner_map_map v v'

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lineEx :
    LineExC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp hK
  haveI : LocallyCompactSpace (KG K (2 + 2)) := hK.isClosed.locallyCompactSpace
  let κ : Measure (KG K (2 + 2)) := Measure.haar
  obtain ⟨⟨c, hc⟩, hvol⟩ := unf μ μ₂ κ
  obtain ⟨S, hfd, hS⟩ := secFD μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂
  have hsf : ∀ f ∈ S, SFun f := fun f hf =>
    secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).1 ((hS f).1 hf).2
  have hsl : ∀ f ∈ S, Slices τ₁ τ₂ f := fun f hf =>
    ((secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).2).1 ((hS f).1 hf).1).2.2.2.2
  obtain ⟨hz, hl, hp, -⟩ := pmLaws μ₂ κ
  obtain ⟨d, sec, hinj, hr, hB⟩ := frame_ex S
    (fun f f' => ((c * volN K : ℝ) : ℂ) * ∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ)
    (fun f hf f' hf' f'' hf'' a => by
      rw [(hl f f' f'' (hsf f hf) (hsf f' hf') (hsf f'' hf'') a).1]; ring)
    (fun f hf f' hf' => by
      rw [map_mul, (hl f f' f' (hsf f hf) (hsf f' hf') (hsf f' hf') 1).2, Complex.conj_ofReal])
    (fun f hf h => by
      rw [Complex.re_ofReal_mul]
      exact mul_pos (mul_pos hc.1 hvol) (hp f (hsf f hf) h))
  have hmem : ∀ v, sec v ∈ S := fun v => hr ▸ LinearMap.mem_range_self sec v
  have hex : ∀ (β : ℝ → ℂ) (v : Eu d), ∃ w : L2 μ, Continuous β → HasCompactSupport β → Reps μ w (theta β (sec v)) := by
    intro β v
    by_cases h : Continuous β ∧ HasCompactSupport β
    · obtain ⟨h1, h2, h3⟩ := bfFun (sec v) β (hsf _ (hmem v)) h.1 h.2
      obtain ⟨w, hw⟩ := ((thBasic μ _ h1.cont h1.rat h2).2.2.2 h3).2.2
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun a b => (h ⟨a, b⟩).elim⟩
  choose T hT using hex
  obtain ⟨J, hJ⟩ := isoExt d T (by
    intro β β' v v' h1 h2 h3 h4
    rw [pairF μ μ₂ κ c hc (sec v) (sec v') β β' (hsf _ (hmem v)) (hsf _ (hmem v')) h1 h2 h3 h4 _ _
      (hT β v h1 h2) (hT β' v' h3 h4), ← hB v v']
    have h0 : ∀ x y, pw μ₂ (sec v) (sec v') x y = 0 := fun x y =>
      (hz τ₁ τ₂ τ₁ τ₂ _ _ (hsf _ (hmem v)) (hsf _ (hmem v')) (hsl _ (hmem v)) (hsl _ (hmem v')) x y).2 hP.orth
    simp only [h0, mul_zero, integral_zero, add_zero]
    push_cast
    ring)
  refine ⟨d, ⟨⟨sec, hinj, fun f => by rw [hr]; exact hS f, J, ?_⟩⟩⟩
  intro β v u h1 h2 hu
  rw [hJ β v u h1 h2 hu]
  exact hT β v h1 h2
