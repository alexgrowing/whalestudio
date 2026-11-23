import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open MeasureTheory Module Set Submodule

noncomputable section

section Tile

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]

def reps (bA bB : Basis ι ℝ V) : Finset V :=
  (ZSpan.setFinite_inter bB (ZSpan.fundamentalDomain_isBounded bA)).toFinset

theorem mem_reps {bA bB : Basis ι ℝ V} {c : V} :
    c ∈ reps bA bB ↔ c ∈ ZSpan.fundamentalDomain bA ∧ c ∈ span ℤ (range bB) := by
  unfold reps
  rw [Set.Finite.mem_toFinset]
  exact Iff.intro (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.1, h.2⟩)

theorem fd_uniq (b : Basis ι ℝ V) {x β1 β2 : V} (h1 : β1 ∈ span ℤ (range b))
    (h2 : β2 ∈ span ℤ (range b)) (hx1 : β1 + x ∈ ZSpan.fundamentalDomain b)
    (hx2 : β2 + x ∈ ZSpan.fundamentalDomain b) : β1 = β2 := by
  have := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b := b) x).unique
    (y₁ := ⟨β1, h1⟩) (y₂ := ⟨β2, h2⟩) hx1 hx2
  exact congrArg Subtype.val this

theorem fd_exists (b : Basis ι ℝ V) (x : V) :
    ∃ β ∈ span ℤ (range b), β + x ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b := b) x
  exact ⟨v, v.2, hv⟩

theorem reps_unique (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (b : V) (hb : b ∈ span ℤ (range bB)) :
    ∃! c, c ∈ reps bA bB ∧ b - c ∈ span ℤ (range bA) := by
  obtain ⟨β, hβ, hβb⟩ := fd_exists bA b
  refine ⟨β + b, ⟨mem_reps.2 ⟨hβb, add_mem (hAB hβ) hb⟩, ?_⟩, ?_⟩
  · have e : b - (β + b) = -β := by abel
    rw [e]
    exact neg_mem hβ
  · rintro c' ⟨hc'R, hc'A⟩
    have hc'F := (mem_reps.1 hc'R).1
    have e := fd_uniq bA (neg_mem hc'A) hβ (x := b)
      (by convert hc'F using 1; abel) hβb
    rw [← e]
    abel

theorem reps_zero (bA bB : Basis ι ℝ V) : (0 : V) ∈ reps bA bB := by
  refine mem_reps.2 ⟨?_, zero_mem _⟩
  simp [ZSpan.mem_fundamentalDomain]

def tileT (bA bB : Basis ι ℝ V) : Set V :=
  ⋃ c ∈ reps bA bB, (fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB

instance cntA (bA : Basis ι ℝ V) : Countable (span ℤ (range bA)).toAddSubgroup :=
  inferInstanceAs (Countable (span ℤ (range bA)))

private theorem mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain {bA bB : Basis ι ℝ V} {x : V} :
    x ∈ tileT bA bB ↔ ∃ c ∈ reps bA bB, x - c ∈ ZSpan.fundamentalDomain bB := by
  unfold tileT
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]

private theorem measurableSet_tileT (bA bB : Basis ι ℝ V) :
    MeasurableSet (tileT bA bB) := by
  unfold tileT
  exact Finset.measurableSet_biUnion _ fun c _ =>
    (ZSpan.fundamentalDomain_measurableSet bB).preimage (continuous_sub_right c).measurable

theorem tile_fund (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (μ : Measure V) :
    IsAddFundamentalDomain (span ℤ (range bA)).toAddSubgroup (tileT bA bB) μ := by
  have hv : ∀ (g : (span ℤ (range bA)).toAddSubgroup) (y : V), g +ᵥ y = (g : V) + y :=
    fun _ _ => rfl
  refine IsAddFundamentalDomain.mk' (measurableSet_tileT bA bB).nullMeasurableSet ?_
  intro x
  obtain ⟨β, hβ, hβx⟩ := fd_exists bB x
  obtain ⟨c, ⟨hc, hc'⟩, huniq⟩ := reps_unique bA bB hAB (-β) (neg_mem hβ)
  have hg : c + β ∈ span ℤ (range bA) := by
    have := neg_mem hc'
    rwa [neg_sub, sub_neg_eq_add] at this
  refine ⟨⟨c + β, hg⟩, ?_, ?_⟩
  · beta_reduce
    rw [hv, mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain]
    refine ⟨c, hc, ?_⟩
    change c + β + x - c ∈ _
    convert hβx using 1
    abel
  · rintro ⟨g, hgA⟩ hgx
    rw [hv, mem_tileT_iff_exists_rep_sub_mem_fundamentalDomain] at hgx
    obtain ⟨c', hc'R, hc'x⟩ := hgx
    change g + x - c' ∈ _ at hc'x
    have hgA' : g ∈ span ℤ (range bA) := hgA
    have hc'B : c' ∈ span ℤ (range bB) := (mem_reps.1 hc'R).2
    have h1 : g - c' = β := fd_uniq bB (sub_mem (hAB hgA') hc'B) hβ
      (by convert hc'x using 1; abel) hβx
    have h2 : c' = c := huniq c' ⟨hc'R, by
      have e : -β - c' = -g := by rw [← h1]; abel
      rw [e]
      exact neg_mem hgA'⟩
    apply Subtype.ext
    change g = c + β
    rw [← h2, ← h1]
    abel

theorem bdd_trans {s : Set V} (hs : Bornology.IsBounded s) (c : V) :
    Bornology.IsBounded ((fun x => x - c) ⁻¹' s) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs
  refine isBounded_iff_forall_norm_le.2 ⟨R + ‖c‖, fun x hx => ?_⟩
  have hxc : ‖x - c‖ ≤ R := hR _ hx
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ R + ‖c‖ := by gcongr

variable (μ : Measure V) [μ.IsAddHaarMeasure]

private theorem isAddFundamentalDomain_zspan_fundamentalDomain (b : Basis ι ℝ V) (μ : Measure V) :
    IsAddFundamentalDomain (span ℤ (range b)).toAddSubgroup (ZSpan.fundamentalDomain b) μ := by
  refine IsAddFundamentalDomain.mk' (ZSpan.fundamentalDomain_measurableSet b).nullMeasurableSet ?_
  intro x
  obtain ⟨β, hβ, hβx⟩ := fd_exists b x
  refine ⟨⟨β, hβ⟩, hβx, ?_⟩
  rintro ⟨g, hg⟩ hgx
  exact Subtype.ext (fd_uniq b hg hβ hgx hβx)

private theorem setIntegral_preimage_sub_of_periodic (h : V → ℝ) (s : Set V) (c : V)
    (hper : ∀ x, h (x + c) = h x) :
    ∫ x in (fun x => x - c) ⁻¹' s, h x ∂μ = ∫ x in s, h x ∂μ := by
  have hf : (fun x : V => x - c) = fun x => -c + x := funext fun x => sub_eq_neg_add x c
  rw [hf]
  have hmp : MeasurePreserving (fun x : V => -c + x) μ μ := measurePreserving_add_left μ (-c)
  have he : MeasurableEmbedding (fun x : V => -c + x) := measurableEmbedding_addLeft (-c)
  calc ∫ x in (fun x => -c + x) ⁻¹' s, h x ∂μ
      = ∫ x in (fun x => -c + x) ⁻¹' s, h ((-c + x) + c) ∂μ := by
        congr 1; ext x; congr 1; abel
    _ = ∫ y in s, h (y + c) ∂μ := hmp.setIntegral_preimage_emb he (fun y => h (y + c)) s
    _ = ∫ y in s, h y ∂μ := by simp only [hper]

private theorem setIntegral_finset_biUnion_of_pairwise_disjoint (h : V → ℝ) (s : V → Set V) :
    ∀ t : Finset V, (∀ i ∈ t, MeasurableSet (s i)) → Set.Pairwise ↑t (Function.onFun Disjoint s) →
      (∀ i ∈ t, IntegrableOn h (s i) μ) →
      ∫ x in ⋃ i ∈ t, s i, h x ∂μ = ∑ i ∈ t, ∫ x in s i, h x ∂μ := by
  classical
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro _ _ _
    simp
  · intro a t ha ih hs hd hf
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn h (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hd' : Set.Pairwise ↑t (Function.onFun Disjoint s) :=
      hd.mono (Finset.coe_subset.2 (Finset.subset_insert a t))
    have hdisj : Disjoint (s a) (⋃ i ∈ t, s i) := by
      refine Set.disjoint_iUnion₂_right.2 fun i hi => ?_
      have hne : a ≠ i := fun e => ha (e ▸ hi)
      exact hd (Finset.mem_coe.2 (Finset.mem_insert_self a t))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) hne
    have hint_r : IntegrableOn h (⋃ i ∈ t, s i) μ := integrableOn_finset_iUnion.2 hf'
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union hdisj (Finset.measurableSet_biUnion t hs') (hf a (Finset.mem_insert_self a t))
        hint_r, ih hs' hd' hf']

theorem tile_integral (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (h : V → ℝ) (hc : Continuous h)
    (hper : ∀ β ∈ span ℤ (range bB), ∀ x, h (x + β) = h x) :
    ∫ x in ZSpan.fundamentalDomain bA, h x ∂μ =
      (reps bA bB).card * ∫ x in ZSpan.fundamentalDomain bB, h x ∂μ := by
  have : VAddInvariantMeasure (span ℤ (range bA)).toAddSubgroup V μ :=
    ⟨fun g s _ => measure_preimage_add μ (g : V) s⟩
  have hA := isAddFundamentalDomain_zspan_fundamentalDomain bA μ
  have hT := tile_fund bA bB hAB μ
  have hperA : ∀ (g : (span ℤ (range bA)).toAddSubgroup) (x : V), h (g +ᵥ x) = h x := by
    intro g x
    have hg : (g : V) ∈ span ℤ (range bA) := g.2
    change h ((g : V) + x) = h x
    rw [add_comm]
    exact hper _ (hAB hg) x
  rw [hA.setIntegral_eq hT hperA]
  unfold tileT
  rw [setIntegral_finset_biUnion_of_pairwise_disjoint μ h (fun c => (fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB)
    (reps bA bB) ?_ ?_ ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => ∫ x in ZSpan.fundamentalDomain bB, h x ∂μ) fun c hc =>
      setIntegral_preimage_sub_of_periodic μ h (ZSpan.fundamentalDomain bB) c (hper c (mem_reps.1 hc).2),
      Finset.sum_const, nsmul_eq_mul]
  · intro c _
    exact (ZSpan.fundamentalDomain_measurableSet bB).preimage (continuous_sub_right c).measurable
  · intro c1 hc1 c2 hc2 hne
    refine Set.disjoint_left.2 fun x hx1 hx2 => hne ?_
    have e := fd_uniq bB
      (neg_mem (mem_reps.1 (Finset.mem_coe.1 hc1)).2)
      (neg_mem (mem_reps.1 (Finset.mem_coe.1 hc2)).2) (x := x)
      (by rw [neg_add_eq_sub]; exact hx1) (by rw [neg_add_eq_sub]; exact hx2)
    exact neg_inj.1 e
  · intro c _
    have hb := bdd_trans (ZSpan.fundamentalDomain_isBounded bB) c
    have hK : IsCompact (closure ((fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB)) := by
      first
        | exact hb.isCompact_closure
        | exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
    first
      | exact ((hc.locallyIntegrable (μ := μ)).integrableOn_isCompact hK).mono_set subset_closure
      | exact (hc.continuousOn.integrableOn_compact hK).mono_set subset_closure
      | exact (hc.integrableOn_isCompact hK).mono_set subset_closure
      | exact (hc.continuousOn.integrableOn_isCompact hK).mono_set subset_closure

theorem tile_measure (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB)) :
    μ.real (ZSpan.fundamentalDomain bA) =
      (reps bA bB).card * μ.real (ZSpan.fundamentalDomain bB) := by
  have := tile_integral μ bA bB hAB (fun _ => (1 : ℝ)) continuous_const
    (fun _ _ _ => rfl)
  simpa [setIntegral_const] using this

theorem tile_average (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (h : V → ℝ) (hc : Continuous h)
    (hper : ∀ β ∈ span ℤ (range bB), ∀ x, h (x + β) = h x) :
    ⨍ x in ZSpan.fundamentalDomain bA, h x ∂μ = ⨍ x in ZSpan.fundamentalDomain bB, h x ∂μ := by
  have hcard : ((reps bA bB).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨0, reps_zero bA bB⟩)
  rw [setAverage_eq, setAverage_eq, tile_integral μ bA bB hAB h hc hper,
    tile_measure μ bA bB hAB, smul_eq_mul, smul_eq_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hcard, one_mul]

end Tile

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
