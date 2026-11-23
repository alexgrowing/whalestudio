import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem cnt_le_sq {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) :
    cnt Γ Ω x ≤ cnt Γ Ω x ^ 2 := by
  by_cases h : ∃ γ : Γ, x⁻¹ * (γ : G) * x ∈ Ω
  · obtain ⟨γ, hγ⟩ := h
    have h1 : 1 ≤ cnt Γ Ω x := by
      have h2 := ENNReal.le_tsum (f := fun γ : Γ => Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x)) γ
      have h3 : Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x) = 1 := by
        rw [Set.indicator_of_mem hγ]; rfl
      rw [h3] at h2
      exact h2
    rw [sq]
    exact le_mul_of_one_le_left zero_le h1
  · have h0 : cnt Γ Ω x = 0 := by
      unfold cnt
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => h ⟨γ, hm⟩) _
    simp [h0]

private theorem cnt_central {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (a x : G)
    (ha : ∀ y, a * y = y * a) : cnt Γ Ω (a * x) = cnt Γ Ω x := by
  unfold cnt
  refine tsum_congr fun γ => ?_
  have e : (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * (γ : G) * x := by
    have h1 : (γ : G) * a = a * (γ : G) := (ha _).symm
    calc (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * a⁻¹ * ((γ : G) * a) * x := by group
      _ = x⁻¹ * (γ : G) * x := by rw [h1]; group
  rw [e]

private theorem norm_part_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : Submodule ℂ V) [K.HasOrthogonalProjection] (U Up : V →L[ℂ] V)
    (h1 : ∀ f ∈ K, Up f = U f) (h2 : ∀ f ∈ Kᗮ, Up f = 0) : ‖Up‖ ≤ ‖U‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have e : Up f = U (K.starProjection f) := by
    have h3 : f = K.starProjection f + (f - K.starProjection f) := by abel
    calc Up f = Up (K.starProjection f) + Up (f - K.starProjection f) := by
          rw [← map_add, ← h3]
      _ = U (K.starProjection f) := by
          rw [h2 _ (K.sub_starProjection_mem_orthogonal f), add_zero,
            h1 _ (K.starProjection_apply_mem f)]
  rw [e]
  refine (U.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le f) (norm_nonneg _)

private theorem le_ofReal_sqrt {e : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : e ^ 2 ≤ ENNReal.ofReal r) :
    e ≤ ENNReal.ofReal (Real.sqrt r) := by
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]
  exact h

private theorem enorm_inner_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a b : V) (T U : V →L[ℂ] V) (hT : ‖T‖ ≤ ‖U‖) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (c : ℝ≥0∞)
    (ha : ‖a‖ₑ ≤ ENNReal.ofReal P) (hb : ‖b‖ₑ ≤ ENNReal.ofReal Q * c) :
    ‖(inner ℂ a (T b) : ℂ)‖ₑ ≤ ENNReal.ofReal (P * Q * ‖U‖) * c := by
  have h1 : ‖(inner ℂ a (T b) : ℂ)‖ ≤ ‖a‖ * (‖U‖ * ‖b‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((T.le_opNorm b).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _))
  calc ‖(inner ℂ a (T b) : ℂ)‖ₑ = ENNReal.ofReal ‖(inner ℂ a (T b) : ℂ)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖a‖ * (‖U‖ * ‖b‖)) := ENNReal.ofReal_le_ofReal h1
    _ = ‖a‖ₑ * (ENNReal.ofReal ‖U‖ * ‖b‖ₑ) := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal ‖U‖ * (ENNReal.ofReal Q * c)) := by gcongr
    _ = ENNReal.ofReal (P * Q * ‖U‖) * c := by
        rw [ENNReal.ofReal_mul (mul_nonneg hP hQ), ENNReal.ofReal_mul hP]
        ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.gBound_pf :
    Basic → GBound := by
  intro hB E _ _ _ n ι _ s
  obtain ⟨-, -, hcomm, -⟩ := hB E n s.pos
  obtain ⟨C₀, Ω, hC₀, hΩ, hk⟩ := s.vecs.norm
  refine ⟨Ω, hΩ, fun x₀ => ?_⟩
  have hfin : cnt (ratH E n 0) Ω x₀ ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ x₀
  have hA : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ (cnt (ratH E n 0) Ω x₀).toReal := ENNReal.toReal_nonneg
  have hAe : ENNReal.ofReal C₀.toReal = C₀ := ENNReal.ofReal_toReal hC₀
  have hce : ENNReal.ofReal (cnt (ratH E n 0) Ω x₀).toReal = cnt (ratH E n 0) Ω x₀ :=
    ENNReal.ofReal_toReal hfin
  refine ⟨(Fintype.card ι : ℝ) * (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal),
    by positivity, fun m t y => ?_⟩
  have hU : ‖m.Uπ‖ ≤ ‖m.U‖ := norm_part_le _ m.U m.Uπ m.pp.1 m.pp.2
  have h1 : ∀ i, ‖s.k₁ (ac E n t * x₀) i‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal)) := fun i => by
    refine le_ofReal_sqrt (mul_nonneg hA hc) ?_
    rw [ENNReal.ofReal_mul hA, hAe, hce, ← cnt_central (ratH E n 0) Ω (ac E n t) x₀ (hcomm t)]
    exact (hk _ i).1
  have h2 : ∀ i, ‖s.k₂ y i‖ₑ ≤ ENNReal.ofReal (Real.sqrt C₀.toReal) * cnt (ratH E n 0) Ω y := fun i => by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hA, hAe]
    exact (hk y i).2.trans (mul_le_mul_right (cnt_le_sq _ _ _) _)
  have h3 : ∀ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := fun i =>
    enorm_inner_le _ _ _ _ hU _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ (h1 i) (h2 i)
  calc ‖m.G (ac E n t * x₀) y‖ₑ ≤ ∑ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := Finset.sum_le_sum fun i _ => h3 i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc (Fintype.card ι : ℝ)]
