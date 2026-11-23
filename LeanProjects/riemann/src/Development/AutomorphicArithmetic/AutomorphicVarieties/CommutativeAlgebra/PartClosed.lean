import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add, h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add, h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem homog_of_span {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) :
    IsHomog O wt (Ideal.span S) := by
  intro f hf j
  have key : ∀ b : MvPowerSeries σ O, ∀ j, wcomp O wt j (b * f) ∈ Ideal.span S := by
    induction hf using Submodule.span_induction with
    | mem a ha =>
      intro b j
      obtain ⟨c, hc⟩ := hS a ha
      rw [wcomp_mul_homog wt hc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ha)
    | zero => intro b j; simp
    | add x y _ _ hx hy =>
      intro b j
      rw [mul_add, map_add]
      exact add_mem (hx b j) (hy b j)
    | smul r x _ hx =>
      intro b j
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _ j
  simpa using key 1 j

private theorem homog_span_pow {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) (N : ℕ) :
    IsHomog O wt (Ideal.span S ^ N) := by
  have key : ∃ T : Set (MvPowerSeries σ O), (∀ a ∈ T, ∃ c, a ∈ wtPart O wt c) ∧
      Ideal.span S ^ N = Ideal.span T := by
    induction N with
    | zero =>
      refine ⟨{1}, ?_, by simp⟩
      rintro a rfl
      exact ⟨0, one_mem_wtPart O wt⟩
    | succ n ih =>
      obtain ⟨T, hT, hT'⟩ := ih
      refine ⟨_, ?_, by rw [pow_succ, hT', Ideal.span_mul_span']⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hT a ha
      obtain ⟨d, hd⟩ := hS b hb
      exact ⟨c + d, mul_mem_wtPart O wt hc hd⟩
  obtain ⟨T, hT, hT'⟩ := key
  rw [hT']
  exact homog_of_span wt T hT

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

theorem UpperTheory.V.Alg.part_closed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (x : R), (∀ N : ℕ, ∃ y ∈ W.part j, x - y ∈ maximalIdeal R ^ N) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ hR W hz j x hx
  classical
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  let S : Set (MvPowerSeries W.σ O) :=
    Set.range MvPowerSeries.X ∪ algebraMap O _ '' (maximalIdeal O : Set O)
  have hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O W.wt c := by
    rintro _ (⟨i, rfl⟩ | ⟨a, -, rfl⟩)
    · exact ⟨_, X_mem_wtPart O W.wt i⟩
    · refine ⟨0, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart O W.wt)
  have hle : (Ideal.span S).map W.π ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact hz i
    · show W.π (algebraMap O _ a) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact fun h => ha (IsLocalHom.map_nonunit a h)
  have hmap : (Ideal.span S).map W.π = maximalIdeal R := by
    refine le_antisymm hle fun r hr => ?_
    obtain ⟨f, rfl⟩ := W.surj r
    have h1 : f - algebraMap O _ (constantCoeff f) ∈ Ideal.span S := by
      refine Ideal.span_mono Set.subset_union_left (mem_span_X _ ?_)
      simp [MvPowerSeries.algebraMap_apply]
    have h2 : constantCoeff f ∈ maximalIdeal O := fun hu =>
      hr ((MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map W.π)
    have h3 : algebraMap O _ (constantCoeff f) ∈ Ideal.span S :=
      Ideal.subset_span (Or.inr ⟨_, h2, rfl⟩)
    exact Ideal.mem_map_of_mem _ (by simpa using add_mem h1 h3)
  obtain ⟨f, rfl⟩ := W.surj x
  have key : ∀ N : ℕ, W.π (f - wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
    intro N
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx N
    rw [← hmap, ← Ideal.map_pow] at hxy ⊢
    obtain ⟨g, hg, hgxy⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hxy
    have h1 : f - y - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, map_sub, hgxy]
      exact sub_self _
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j y = y := by
      ext n
      rw [coeff_wcomp]
      split_ifs with h
      · rfl
      · exact (hy n h).symm
    have h4 : g - wcomp O W.wt j g ∈ Ideal.span S ^ N :=
      sub_mem hg (homog_span_pow W.wt S hS N g hg j)
    have h5 : f - wcomp O W.wt j f =
        (f - y - g) - wcomp O W.wt j (f - y - g) + (g - wcomp O W.wt j g) := by
      rw [map_sub, map_sub, h3]; ring
    rw [h5, map_add, (RingHom.mem_ker).1 (sub_mem h1 h2), zero_add]
    exact Ideal.mem_map_of_mem _ h4
  have h0 : W.π (f - wcomp O W.wt j f) = 0 := by
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
    exact key
  rw [map_sub, sub_eq_zero] at h0
  exact ⟨_, wcomp_mem O W.wt j f, h0.symm⟩
