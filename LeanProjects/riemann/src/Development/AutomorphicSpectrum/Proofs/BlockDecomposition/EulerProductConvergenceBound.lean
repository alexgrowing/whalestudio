import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.SumDev

theorem sum_prod_le {ι X : Type*} (D : Finset ι) (B : Finset X) (e : ι → X → ℝ) (P : ι → X → Prop)
    (a b c : ι → ℝ) (w C' : ℝ) (hw : 0 ≤ w)
    (ha : ∀ v ∈ D, 0 ≤ a v) (hb : ∀ v ∈ D, 0 ≤ b v) (hbc : ∀ v ∈ D, b v * c v = a v)
    (he0 : ∀ v ∈ D, ∀ x ∈ B, 0 ≤ e v x)
    (he : ∀ v ∈ D, ∀ x ∈ B, e v x ≤ a v + if P v x then b v else 0)
    (hcount : ∀ t ⊆ D, w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) ≤ C' * ∏ v ∈ t, c v) :
    w * ∑ x ∈ B, ∏ v ∈ D, e v x ≤ C' * ∏ v ∈ D, (2 * a v) := by
  have hx : ∀ x ∈ B, ∏ v ∈ D, e v x ≤
      ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
    intro x hxB
    calc ∏ v ∈ D, e v x ≤ ∏ v ∈ D, ((if P v x then b v else 0) + a v) := by
          refine Finset.prod_le_prod (fun v hv => he0 v hv x hxB) (fun v hv => ?_)
          rw [add_comm]
          exact he v hv x hxB
      _ = ∑ t ∈ D.powerset, (∏ v ∈ t, (if P v x then b v else 0)) * ∏ v ∈ D \ t, a v :=
          Finset.prod_add _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_ite_zero]
  have ht : ∀ t ∈ D.powerset,
      w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v ≤ C' * ∏ v ∈ D, a v := by
    intro t htD
    rw [Finset.mem_powerset] at htD
    have hA : 0 ≤ ∏ v ∈ D \ t, a v := Finset.prod_nonneg fun v hv => ha v (Finset.sdiff_subset hv)
    have hB : 0 ≤ ∏ v ∈ t, b v := Finset.prod_nonneg fun v hv => hb v (htD hv)
    have hsum : ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v
        = ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    have hprod : (∏ v ∈ t, b v) * ∏ v ∈ t, c v = ∏ v ∈ t, a v := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v hv => hbc v (htD hv)
    rw [hsum]
    calc w * (((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v))
        = (w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ)) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
          ring
      _ ≤ (C' * ∏ v ∈ t, c v) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) :=
          mul_le_mul_of_nonneg_right (hcount t htD) (mul_nonneg hB hA)
      _ = C' * ((∏ v ∈ D \ t, a v) * ((∏ v ∈ t, b v) * ∏ v ∈ t, c v)) := by ring
      _ = C' * ∏ v ∈ D, a v := by rw [hprod, Finset.prod_sdiff htD]
  calc w * ∑ x ∈ B, ∏ v ∈ D, e v x
      ≤ w * ∑ x ∈ B, ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) hw
    _ = ∑ t ∈ D.powerset, w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ t ∈ D.powerset, C' * ∏ v ∈ D, a v := Finset.sum_le_sum ht
    _ = C' * ∏ v ∈ D, (2 * a v) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.prod_mul_distrib, Finset.prod_const, nsmul_eq_mul]
        push_cast
        ring

variable {F : Type} [Field F] [NumberField F]

theorem mem_asIdeal (v : HeightOneSpectrum (𝓞 F)) {x : F}
    (hxi : algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F)
    (h1 : Valued.v (algebraMap F (Fv F v) x) ≠ 1) {N : ℕ} {y : 𝓞 F} (hy : (y : F) = (N : F) * x) :
    y ∈ v.asIdeal := by
  have hval : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hle : v.valuation F x ≤ 1 := by
    rw [← hval]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hxi
  have hlt : v.valuation F x < 1 := lt_of_le_of_ne hle (by rw [← hval]; exact h1)
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v y).mp ?_
  have hN : v.valuation F (N : F) ≤ 1 := by
    have h := HeightOneSpectrum.valuation_le_one (K := F) v (N : 𝓞 F)
    exact_mod_cast h
  have hNx : v.valuation F ((N : F) * x) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hN) hlt
  convert hNx using 2

theorem mem_prod_asIdeal (t : Finset (HeightOneSpectrum (𝓞 F))) {y : 𝓞 F} (h : ∀ v ∈ t, y ∈ v.asIdeal) :
    y ∈ ∏ v ∈ t, v.asIdeal := by
  revert h
  refine Finset.induction_on t (fun _ => by simp) ?_
  intro v t hv ih h
  rw [Finset.prod_insert hv]
  have hcop : IsCoprime v.asIdeal (∏ w ∈ t, w.asIdeal) := by
    refine IsCoprime.prod_right fun w hw => ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal fun hvw => hv ?_
    rw [HeightOneSpectrum.ext hvw]
    exact hw
  rw [Ideal.mul_eq_inf_of_isCoprime hcop]
  exact Ideal.mem_inf.mpr ⟨h v (Finset.mem_insert_self v t), ih fun w hw => h w (Finset.mem_insert_of_mem hw)⟩

theorem sum_bounded_prod : CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), 0 ≤ C → (∀ v, v ∉ S → (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧ ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ δ : ℝ, 0 < δ → ∀ D : Finset (HeightOneSpectrum (𝓞 F)), Disjoint D S → ∀ B : Finset F, (∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ (∃ y : 𝓞 F, (y : F) = (N : F) * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K) → δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤ C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
  intro hCB F _ _ hF θ hθ K hK N hN
  obtain ⟨C0, hC0⟩ := hCB F hF θ hθ K hK N hN
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro S C g hC hg δ hδ D hDS B hB
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := fun v =>
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hcnt : ∀ t ⊆ D, δ ^ Module.finrank ℚ F *
      ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ) ≤
        max C0 0 * ∏ v ∈ t, (1 / (Ideal.absNorm v.asIdeal : ℝ)) := by
    intro t ht
    have hI0 : (∏ v ∈ t, v.asIdeal) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      intro v _
      rw [Ideal.zero_eq_bot]
      exact v.ne_bot
    obtain ⟨hfin, hle⟩ := hC0 δ hδ (∏ v ∈ t, v.asIdeal) hI0
    have hsub : (↑(B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1) : Set F) ⊆
        {x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K} := by
      intro x hx
      rw [Finset.coe_filter] at hx
      obtain ⟨hxB, hxP⟩ := hx
      obtain ⟨hx0, hxS, ⟨y, hy⟩, hxK⟩ := hB x hxB
      refine ⟨hx0, ⟨y, mem_prod_asIdeal t fun v hv => ?_, hy⟩, hxK⟩
      have hvS : v ∉ S := Finset.disjoint_left.mp hDS (ht hv)
      exact mem_asIdeal v (hxS v hvS) (hxP v hv) hy
    have hcard : ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ) ≤
        ({x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K}.ncard : ℝ) := by
      rw [← Set.ncard_coe_finset]
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have hnormI : (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) = ∏ v ∈ t, (Ideal.absNorm v.asIdeal : ℝ) := by
      rw [map_prod, Nat.cast_prod]
    calc δ ^ Module.finrank ℚ F *
          ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ)
        ≤ δ ^ Module.finrank ℚ F * ({x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K}.ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (pow_nonneg hδ.le _)
      _ ≤ C0 / (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) := hle
      _ ≤ max C0 0 / (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      _ = max C0 0 * ∏ v ∈ t, (1 / (Ideal.absNorm v.asIdeal : ℝ)) := by
          rw [hnormI, Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
  have key := sum_prod_le D B (fun v x => |g v (algebraMap F (Fv F v) x) - 1|)
    (fun v x => Valued.v (algebraMap F (Fv F v) x) ≠ 1)
    (fun v => C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) (fun v => C / (Ideal.absNorm v.asIdeal : ℝ))
    (fun v => 1 / (Ideal.absNorm v.asIdeal : ℝ)) (δ ^ Module.finrank ℚ F) (max C0 0)
    (pow_nonneg hδ.le _)
    (fun v _ => div_nonneg hC (pow_nonneg (hnorm v).le _))
    (fun v _ => div_nonneg hC (hnorm v).le)
    (fun v _ => by ring)
    (fun v _ x _ => abs_nonneg _)
    (fun v hv x hx => by
      have hvS : v ∉ S := Finset.disjoint_left.mp hDS hv
      obtain ⟨hx0, hxS, -, -⟩ := hB x hx
      have hint : algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := hxS v hvS
      have h2 : 0 ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := div_nonneg hC (pow_nonneg (hnorm v).le _)
      split_ifs with hP
      · have h1 := (hg v hvS).1 _ hint ((map_ne_zero _).mpr hx0)
        linarith
      · rw [add_zero]
        exact (hg v hvS).2 _ (not_not.mp hP))
    (fun t ht => by
      convert hcnt t ht)
  refine le_of_le_of_eq key ?_
  refine congrArg _ (Finset.prod_congr rfl fun v _ => ?_)
  exact (mul_div_assoc _ _ _).symm

end GlobalTheory.CompanionTheory.Mass.SumDev

end
