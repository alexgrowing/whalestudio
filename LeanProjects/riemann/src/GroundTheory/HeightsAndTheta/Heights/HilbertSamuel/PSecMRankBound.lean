import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SecMRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem finite_secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Module.Finite ℤ (secM y d) := by
  have h := SectionLatticeFinite.secM_fg y d
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (secM y d), ← Submodule.fg_iff_addSubgroup_fg] at h
  exact Module.Finite.iff_fg.mpr h

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) :
    aeval y g = 0 := by
  have hext : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  have h0 : mConeMap y g = 0 := hg
  rw [← hext, AlgHom.comp_apply, h0, map_zero]

variable [DecidableEq K]

theorem finrank_secM_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    Module.finrank ℤ (secM y d) ≤
      Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) d) := by
  have hI : ∀ f ∈ KH.genIdeal y, aeval y f = 0 := by
    have hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
      unfold KH.genIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval y (map (algebraMap ℤ ℚ) g) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem hg
    exact fun f hf => hle hf
  let ψ : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω :=
    (Ideal.Quotient.liftₐ (KH.genIdeal y) (aeval y) hI).toLinearMap
  let V := NumbersDVR.gradedPiece (KH.genIdeal y) d
  have : FiniteDimensional ℚ V := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) d).1
  let R : Submodule ℚ Ω := V.map ψ
  have : FiniteDimensional ℚ R := Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map ψ)
  have hsub : ∀ s ∈ secM y d, s ∈ R := by
    intro s hs
    have hspan : Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ aeval y g = s} ≤
        R.restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨Ideal.Quotient.mk _ (map (Int.castRingHom ℚ) g), ⟨map (Int.castRingHom ℚ) g, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
        exact (Bridge.isMultiHomog_iff _ _).mpr fun m hm k => hg m (support_map_subset _ _ hm) k
      · change aeval y (map (Int.castRingHom ℚ) g) = aeval y g
        rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hspan hs
  have := finite_secM y d
  have : Module.IsTorsionFree ℤ (secM y d) :=
    Function.Injective.moduleIsTorsionFree (secM y d).subtype Subtype.val_injective (fun _ _ => rfl)
  let bs := Module.Free.chooseBasis ℤ (secM y d)
  let v : Module.Free.ChooseBasisIndex ℤ (secM y d) → Ω := fun i => (bs i : Ω)
  have hliZ : LinearIndependent ℤ v :=
    bs.linearIndependent.map' (secM y d).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_span_eq_card hliQ]
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range v)) ≤ Module.finrank ℚ R :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hsub _ (bs i).2))
    _ ≤ Module.finrank ℚ V := Submodule.finrank_map_le ψ V

theorem proof (h : GenericFibreVar.Statement) : SecMRankBound.Statement := by
  intro K _ ι _ Ω _ y D b hvar hb
  classical

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  refine ⟨fun m => finite_secM y _, ?_⟩

  obtain ⟨⟨hprime, hhom, -⟩, hdim⟩ := h K ι Ω y D hvar
  have hlt : ringKrullDim (MRingOver ℚ ι ⧸ KH.genIdeal y) <
      (((D + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : D + Fintype.card K < D + 1 + Fintype.card K)
  have hdeg := NumbersDVR.HilbDegBound.full ℚ K ι (D + 1) (KH.genIdeal y) hprime
    ((Bridge.isMultiHomogIdeal_iff _).mpr hhom) hlt
  obtain ⟨a₀, C, hC⟩ := DegLTGrowth.proof K (D + 1) _ hdeg
  have hexp : ((D + 1 : ℕ) : ℝ) - 1 = ((D : ℕ) : ℝ) := by push_cast; ring

  have hrank : ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤
      |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
    intro m
    have e := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) (fun k => m * b k)).2
    have hle := finrank_secM_le y (fun k => m * b k)
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ (Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) (fun k => m * b k)) : ℝ) := by
          exact_mod_cast hle
      _ = |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
          rw [e]; simp
  set B : ℝ := ∑ k, (b k : ℝ) with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  set M0 : ℝ := ∑ j ∈ Finset.range a₀, (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ) with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun j _ => by positivity
  have hC1 : 0 ≤ max C 0 * (B + 1) ^ D := by positivity
  refine ⟨max C 0 * (B + 1) ^ D + M0, by positivity, fun m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hpow1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ D := one_le_pow₀ (by linarith)
  rcases lt_or_ge m a₀ with hm | hm
  ·
    have h1 : (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ M0 :=
      Finset.single_le_sum (f := fun j => (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr hm)
    nlinarith
  ·
    have hg := hC (fun k => m * b k) (fun k => le_trans hm (Nat.le_mul_of_pos_right m (hb k)))
    rw [hexp, Real.rpow_natCast] at hg
    have hsum : (∑ k, (((m * b k : ℕ)) : ℝ)) = m * B := by
      rw [hBdef, Finset.mul_sum]; push_cast; rfl
    have hX : (m : ℝ) * B + 1 ≤ (B + 1) * ((m : ℝ) + 1) := by nlinarith
    have hXpow : ((m : ℝ) * B + 1) ^ D ≤ ((B + 1) * ((m : ℝ) + 1)) ^ D :=
      pow_le_pow_left₀ (by positivity) hX D
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := hrank m
      _ ≤ C * ((∑ k, (((m * b k : ℕ)) : ℝ)) + 1) ^ D := hg
      _ = C * ((m : ℝ) * B + 1) ^ D := by rw [hsum]
      _ ≤ max C 0 * ((m : ℝ) * B + 1) ^ D :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((B + 1) * ((m : ℝ) + 1)) ^ D :=
          mul_le_mul_of_nonneg_left hXpow (le_max_right _ _)
      _ = max C 0 * (B + 1) ^ D * ((m : ℝ) + 1) ^ D := by rw [mul_pow]; ring
      _ ≤ (max C 0 * (B + 1) ^ D + M0) * ((m : ℝ) + 1) ^ D := by nlinarith

theorem full : SecMRankBound.Statement := proof GenericFibreVar.proof

end SecMRankBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
