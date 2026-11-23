import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_intBasis {K : Type} [Field K] [CharZero K] (Λ : AddSubgroup K) (hΛ : Λ.FG) :
    ∃ f : Fin (Module.finrank ℤ Λ) → K, LinearIndependent ℤ f ∧ AddSubgroup.closure (Set.range f) = Λ ∧
      ∀ i, f i ∈ Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Λ
  refine ⟨fun i => (b i : K), ?_, le_antisymm ?_ ?_, fun i => (b i).2⟩
  · exact b.linearIndependent.map' Λ.subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · exact (AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => (b i).2)
  · intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    change _ = x at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [AddSubgroupClass.coe_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => (b i : K)) i)) _

theorem tendsto_logCount_sub_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro HA k _ X _ p D hX hS P a hP ha Λ hΛ
  obtain ⟨C, hC1, hCs⟩ := hΛ.small
  refine ⟨Real.log C + 1, ?_⟩
  intro u B a' hB hu hup ha' t ht
  have := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (germ_injective_of_isIntegral X (U := ⊤) _ trivial)
  choose f hli hcl hmemΛ using fun m => exists_intBasis (Λ m) (hΛ.fg m)
  let ω : ∀ σ, VolDens p σ D := fun σ => Classical.choice (GlobalTheory.T.exists_smoothVolumeDensityChart_projArith k X p D hX hS σ)
  have hmem : ∀ (m : ℕ) i, f m i ∈ P.H m 1 := fun m i => hΛ.le m (hmemΛ m i)
  have hmem' : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P u).H m 1 := fun m i => by
    rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).1]; exact hmem m i
  have hC1' : 1 ≤ C * Real.exp B := one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hB)
  have hlog : Real.log (C * Real.exp B) = Real.log C + B := by
    rw [Real.log_mul (by positivity) (Real.exp_pos B).ne', Real.log_exp]
  have hs : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    intro m hm; rw [hcl m]; exact hCs m hm
  have hs' : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn (upperParabolic P u) (AddSubgroup.closure (Set.range (f m))) m 1 ((C * Real.exp B) ^ m)) := by
    intro m hm
    rw [hcl m]
    refine (hCs m hm).trans (AddSubgroup.closure_mono ?_)
    rintro x ⟨hx, hb⟩
    refine ⟨hx, fun σ y => ?_⟩
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y x).2]
    have h0 : 0 ≤ P.nu m 1 σ y x := by rw [← norm_val]; exact norm_nonneg _
    rw [mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul (hb σ y) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hu' := (abs_le.1 (hu σ y)).1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (neg_le.1 hu') hm0, mul_nonneg hm0 hB]
  have h1 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS P hP ω _ f hmem hli _ hΛ.rank C hC1 hs t (by linarith)
  have h2 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS (upperParabolic P u) hup ω _ f hmem' hli _ hΛ.rank (C * Real.exp B) hC1' hs' t
    (by rw [hlog]; linarith)
  have h3 := GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric HA k X p D hX hS P hP ω _ f hmem hli hΛ.rank u a a' hup ha ha'
  simp only [hcl] at h1 h2
  have key := (h2.sub h1).add (h3.div_const 2)
  convert key using 1
  · funext m; ring
  · congr 1; ring

end GlobalTheory.HSAmp
