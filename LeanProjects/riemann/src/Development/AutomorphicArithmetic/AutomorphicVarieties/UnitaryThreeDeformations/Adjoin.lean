import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem exists_min_basis {σ : Type} [Finite σ] (S : Set (σ →₀ ℕ)) :
    ∃ B : Finset (σ →₀ ℕ), (∀ b ∈ B, b ∈ S) ∧ ∀ n ∈ S, ∃ b ∈ B, b ≤ n := by
  classical
  have hP : ∀ t : Set (σ →₀ ℕ), t.IsPWO := fun t => Set.isPWO_of_wellQuasiOrderedLE t
  have hfin : {b | Minimal (· ∈ S) b}.Finite :=
    (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn (hP _)
  refine ⟨hfin.toFinset, fun b hb => ?_, fun n hn => ?_⟩
  · exact ((Set.Finite.mem_toFinset hfin).1 hb).1
  · obtain ⟨b, hbn, hb⟩ := (hP S).exists_le_minimal hn
    exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hb, hbn⟩

private theorem exists_decomp {O σ : Type} [CommRing O] [Finite σ] (w : σ → ℤ) (j : ℤ) (S : Set (σ →₀ ℕ))
    (hS : ∀ n ∈ S, Finsupp.weight w n = j) :
    ∃ B : Finset (σ →₀ ℕ), (∀ b ∈ B, b ∈ S) ∧ ∀ f : MvPowerSeries σ O, (∀ n ∉ S, MvPowerSeries.coeff n f = 0) →
      ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ b ∈ B, g b ∈ wtPart O w 0) ∧
        f = ∑ b ∈ B, MvPowerSeries.monomial b 1 * g b := by
  classical
  obtain ⟨B, hBS, hB⟩ := exists_min_basis S
  let c : (σ →₀ ℕ) → (σ →₀ ℕ) := fun n => if h : n ∈ S then Classical.choose (hB n h) else 0
  have hc : ∀ n ∈ S, c n ∈ B ∧ c n ≤ n := by
    intro n hn
    simp only [c, dif_pos hn]
    exact Classical.choose_spec (hB n hn)
  refine ⟨B, hBS, fun f hf => ?_⟩
  let g : (σ →₀ ℕ) → MvPowerSeries σ O := fun b m =>
    if m + b ∈ S ∧ c (m + b) = b then MvPowerSeries.coeff (m + b) f else 0
  have hg : ∀ b n, b ≤ n → MvPowerSeries.coeff (n - b) (g b) =
      if n ∈ S ∧ c n = b then MvPowerSeries.coeff n f else 0 := by
    intro b n hbn
    rw [MvPowerSeries.coeff_apply]
    simp only [g, tsub_add_cancel_of_le hbn]
  refine ⟨g, fun b hb => ?_, ?_⟩
  · intro m hm
    rw [MvPowerSeries.coeff_apply]
    simp only [g]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hm
    have e1 := hS _ h1
    have e2 := hS _ (hBS _ hb)
    rw [map_add] at e1
    omega
  · ext n
    rw [map_sum]
    simp_rw [MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hn : n ∈ S
    · rw [Finset.sum_eq_single (c n)]
      · rw [if_pos (hc n hn).2, hg _ _ (hc n hn).2, if_pos ⟨hn, rfl⟩]
      · intro b _ hb
        split_ifs with hbn
        · rw [hg _ _ hbn, if_neg]
          rintro ⟨_, h⟩
          exact hb h.symm
        · rfl
      · intro h
        exact absurd (hc n hn).1 h
    · rw [hf n hn]
      symm
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hbn
      · rw [hg _ _ hbn, if_neg]
        rintro ⟨h, _⟩
        exact hn h
      · rfl

private theorem inv_mem_wtPart {O σ : Type} [CommRing O] (w : σ → ℤ) {f g : MvPowerSeries σ O}
    (hf : f ∈ wtPart O w 0) (hfg : f * g = 1) : g ∈ wtPart O w 0 := by
  classical
  set g0 := wcomp O w 0 g with hg0
  have h0 : ∀ n, Finsupp.weight w n = 0 → MvPowerSeries.coeff n (g - g0) = 0 := by
    intro n hn
    rw [map_sub, hg0, coeff_wcomp, if_pos hn, sub_self]
  have hprod : ∀ n, Finsupp.weight w n = 0 → MvPowerSeries.coeff n (f * (g - g0)) = 0 := by
    intro n hn
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : Finsupp.weight w p.1 = 0
    · have h2 : Finsupp.weight w p.2 = 0 := by
        have := congrArg (Finsupp.weight w) hp
        rw [map_add] at this
        omega
      rw [h0 _ h2, mul_zero]
    · rw [hf _ h1, zero_mul]
  have hmem : f * (g - g0) ∈ wtPart O w 0 := by
    have e : f * (g - g0) = 1 - f * g0 := by rw [mul_sub, hfg]
    rw [e]
    have h := mul_mem_wtPart O w hf (wcomp_mem O w 0 g)
    rw [add_zero] at h
    exact Submodule.sub_mem _ (one_mem_wtPart O w) h
  have hz : f * (g - g0) = 0 := by
    ext n
    rw [map_zero]
    by_cases hn : Finsupp.weight w n = 0
    · exact hprod n hn
    · exact hmem n hn
  have hgg : g - g0 = 0 := by
    calc g - g0 = g * (f * (g - g0)) := by rw [← mul_assoc, mul_comm g f, hfg, one_mul]
      _ = 0 := by rw [hz, mul_zero]
  have hg : g = g0 := sub_eq_zero.mp hgg
  rw [hg]
  exact wcomp_mem O w 0 g

private theorem monomial_mem_wtPart {O σ : Type} [CommRing O] (w : σ → ℤ) (b : σ →₀ ℕ) :
    (MvPowerSeries.monomial b 1 : MvPowerSeries σ O) ∈ wtPart O w (Finsupp.weight w b) := fun n hn => by
  classical
  rw [MvPowerSeries.coeff_monomial, if_neg]
  rintro rfl
  exact hn rfl

private theorem monomial_mem_adjoin {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R)
    (b : W.σ →₀ ℕ) : W.π (MvPowerSeries.monomial b 1) ∈ Algebra.adjoin O (Set.range W.z) := by
  classical
  induction b using Finsupp.induction with
  | zero =>
    have e : (MvPowerSeries.monomial (0 : W.σ →₀ ℕ) (1 : O)) = 1 := by simp
    rw [e, map_one]
    exact Subalgebra.one_mem _
  | single_add i k b _ _ ih =>
    rw [← mul_one (1 : O), ← MvPowerSeries.monomial_mul_monomial, map_mul, ← MvPowerSeries.X_pow_eq, map_pow]
    have hi : W.π (MvPowerSeries.X i) ∈ Algebra.adjoin O (Set.range W.z) :=
      Algebra.subset_adjoin (Set.mem_range.mpr ⟨i, rfl⟩)
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hi _) ih

private theorem part_decomp {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (j : ℤ) :
    ∃ B : Finset (W.σ →₀ ℕ), W.part j =
      ⨆ b ∈ B, (W.part 0).map (LinearMap.mulLeft O (W.π (MvPowerSeries.monomial b 1))) := by
  obtain ⟨B, hB, hd⟩ := exists_decomp (O := O) W.wt j {n | Finsupp.weight W.wt n = j} fun _ h => h
  refine ⟨B, le_antisymm ?_ (iSup₂_le fun b hb => ?_)⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hd f hf
    rw [map_sum]
    refine sum_mem fun b hb => ?_
    refine Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb ⟨W.π (g b), ⟨g b, hg b hb, rfl⟩, ?_⟩)
    simp
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨MvPowerSeries.monomial b 1 * g, ?_, by simp⟩
    have := mul_mem_wtPart O W.wt (monomial_mem_wtPart W.wt b) hg
    rwa [add_zero, hB b hb] at this

private theorem mem_adjoin_of_mul_eq_one_of_isIntegral' {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {u v : R}
    (huv : u * v = 1) (hv : IsIntegral O v) : v ∈ Algebra.adjoin O {u} := by
  obtain ⟨p, hpm, hp⟩ := hv
  letI : Invertible v := ⟨u, huv, by rw [mul_comm]; exact huv⟩
  have h1 : Polynomial.eval₂ (algebraMap O R) u p.reverse = 0 := by
    have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O R) v p
    rw [hp] at h
    have hinv : (⅟v : R) = u := rfl
    rw [hinv] at h
    have hu : IsUnit (v ^ p.natDegree) := (isUnit_of_invertible v).pow _
    exact hu.mul_left_eq_zero.mp h
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p.reverse)
  rw [Polynomial.coeff_zero_reverse, hpm.leadingCoeff, map_one] at hq
  have h2 : p.reverse = 1 + Polynomial.X * q := by rw [← hq]; ring
  rw [h2, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_one] at h1
  have h3 : v = -Polynomial.aeval u q := by
    have h4 : v * (1 + u * Polynomial.eval₂ (algebraMap O R) u q) = 0 := by rw [h1, mul_zero]
    rw [Polynomial.aeval_def]
    linear_combination h4 - (Polynomial.eval₂ (algebraMap O R) u q) * huv
  rw [h3]
  exact Subalgebra.neg_mem _ (Polynomial.aeval_mem_adjoin_singleton O u)

private theorem part_zero_le {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (W : WPres O ℤ R) (hfin : (W.part 0).FG) : ∀ x ∈ W.part 0, x ∈ Algebra.adjoin O (Set.range W.z) := by
  classical
  haveI := W.fin
  obtain ⟨B, hBS, hB⟩ := exists_decomp (O := O) W.wt 0 {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0}
    (fun n hn => hn.1)
  have hone : (1 : R) ∈ W.part 0 := ⟨1, one_mem_wtPart O W.wt, map_one W.π⟩
  have hmul : ∀ x y, x ∈ W.part 0 → y ∈ W.part 0 → x * y ∈ W.part 0 := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨f * g, ?_, ?_⟩
    · simpa using mul_mem_wtPart O W.wt hf hg
    · simp
  let R0s : Subalgebra O R := Submodule.toSubalgebra (W.part 0) hone hmul
  have hint : ∀ x ∈ W.part 0, IsIntegral O x := fun x hx =>
    IsIntegral.of_mem_of_fg R0s (by rw [Submodule.toSubalgebra_toSubmodule]; exact hfin) x hx
  let zz : (W.σ →₀ ℕ) → R := fun b => W.π (MvPowerSeries.monomial b 1)
  have hmono : ∀ b ∈ B, MvPowerSeries.monomial b (1 : O) ∈ wtPart O W.wt 0 := by
    intro b hb
    have h := monomial_mem_wtPart (O := O) W.wt b
    rwa [(hBS b hb).1] at h
  have hzz : ∀ b ∈ B, zz b ∈ W.part 0 := fun b hb => ⟨_, hmono b hb, rfl⟩
  let A : Subalgebra O R := Algebra.adjoin O (zz '' (B : Set (W.σ →₀ ℕ)))
  have hAR0 : ∀ a ∈ A, a ∈ W.part 0 := by
    intro a ha
    exact (Algebra.adjoin_le (S := R0s) (by rintro _ ⟨b, hb, rfl⟩; exact hzz b hb)) ha
  have hAT : A ≤ Algebra.adjoin O (Set.range W.z) :=
    Algebra.adjoin_le (by rintro _ ⟨b, _, rfl⟩; exact monomial_mem_adjoin W b)
  let I : Ideal A := Ideal.span {a : A | ∃ b ∈ B, (a : R) = zz b}
  have hJ : ∀ x ∈ I, ∃ h ∈ wtPart O W.wt 0, MvPowerSeries.constantCoeff h = 0 ∧ W.π h = (x : R) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, hxb⟩ := hx
      refine ⟨MvPowerSeries.monomial b 1, hmono b hb, ?_, hxb.symm⟩
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial,
        if_neg (Ne.symm (hBS b hb).2)]
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨h1, m1, c1, e1⟩ := hx
      obtain ⟨h2, m2, c2, e2⟩ := hy
      refine ⟨h1 + h2, Submodule.add_mem _ m1 m2, by rw [map_add, c1, c2, add_zero], ?_⟩
      rw [map_add, e1, e2]
      rfl
    | smul a x _ hx =>
      obtain ⟨h1, m1, c1, e1⟩ := hx
      obtain ⟨g, hg, eg⟩ := hAR0 a a.2
      refine ⟨g * h1, ?_, by rw [map_mul, c1, mul_zero], ?_⟩
      · simpa using mul_mem_wtPart O W.wt hg m1
      · show W.π (g * h1) = (a : R) * (x : R)
        rw [map_mul, e1, ← eg]
        rfl
  have hjac : I ≤ (⊥ : Ideal A).jacobson := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    have hxy : x * y ∈ I := I.mul_mem_right y hx
    obtain ⟨h, hh, hc, he⟩ := hJ _ hxy
    have hunit : IsUnit (h + 1) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hc, map_one, zero_add]
      exact isUnit_one
    obtain ⟨g, hg⟩ : ∃ g, (h + 1) * g = 1 := ⟨_, hunit.mul_val_inv⟩
    have hgm : g ∈ wtPart O W.wt 0 :=
      inv_mem_wtPart W.wt (Submodule.add_mem _ hh (one_mem_wtPart O W.wt)) hg
    have hu : ((x * y + 1 : A) : R) * W.π g = 1 := by
      have h3 := congrArg W.π hg
      simp only [map_mul, map_add, map_one, he] at h3
      simpa using h3
    have hvA : W.π g ∈ A := by
      have hv := mem_adjoin_of_mul_eq_one_of_isIntegral' hu (hint _ ⟨g, hgm, rfl⟩)
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr (x * y + 1).2) hv
    exact IsUnit.of_mul_eq_one (⟨W.π g, hvA⟩ : A) (Subtype.ext hu)
  obtain ⟨s, hs⟩ := hfin
  let N' : Submodule A R := Submodule.span A (s : Set R)
  let N : Submodule A R := Submodule.span A {1}
  have hsub : ∀ x ∈ W.part 0, x ∈ N' := by
    intro x hx
    rw [← hs] at hx
    exact Submodule.span_le_restrictScalars O A (s : Set R) hx
  have hle : N' ≤ N ⊔ I • N' := by
    rw [Submodule.span_le]
    intro x hx
    have hx0 : x ∈ W.part 0 := by
      rw [← hs]
      exact Submodule.subset_span hx
    obtain ⟨f, hf, rfl⟩ := hx0
    set c := MvPowerSeries.constantCoeff f with hcdef
    have hf' : ∀ n ∉ {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0},
        MvPowerSeries.coeff n (f - MvPowerSeries.C c) = 0 := by
      intro n hn
      simp only [Set.mem_setOf_eq, not_and, not_not] at hn
      by_cases h0 : n = 0
      · subst h0
        rw [map_sub, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          sub_self]
      · rw [map_sub, MvPowerSeries.coeff_C, if_neg h0, sub_zero]
        by_cases hw : Finsupp.weight W.wt n = 0
        · exact absurd (hn hw) h0
        · exact hf n hw
    obtain ⟨g, hg, hfg⟩ := hB _ hf'
    have hf2 : f = MvPowerSeries.C c + ∑ b ∈ B, MvPowerSeries.monomial b 1 * g b := by
      rw [← hfg]
      ring
    have hval : W.π.toLinearMap f = algebraMap O R c + ∑ b ∈ B, zz b * W.π (g b) := by
      show W.π f = _
      rw [hf2, map_add, map_sum, MvPowerSeries.c_eq_algebraMap, W.π.commutes]
      simp only [map_mul, zz]
    show _ ∈ N ⊔ I • N'
    rw [hval]
    apply Submodule.add_mem_sup
    · have hc1 : algebraMap O R c = (algebraMap O A c) • (1 : R) := by
        rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
        rfl
      rw [hc1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · apply Submodule.sum_mem
      intro b hb
      have hzA : zz b ∈ A := Algebra.subset_adjoin ⟨b, hb, rfl⟩
      have hmemI : (⟨zz b, hzA⟩ : A) ∈ I := Ideal.subset_span ⟨b, hb, rfl⟩
      have hgN : W.π (g b) ∈ N' := hsub _ ⟨g b, hg b hb, rfl⟩
      exact Submodule.smul_mem_smul hmemI hgN
  have hfinal := Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span s.finite_toSet) hjac hle
  intro x hx
  have hxN : x ∈ N := hfinal (hsub x hx)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxN
  rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
  exact hAT a.2

theorem UpperTheory.V.UnitaryThreeInertia.sring_eq_adjoin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → Sring O u = Algebra.adjoin O {x | ∃ g a b, F.η g = 1 ∧ x = (u g).mat a b} ∧ ∀ j, Module.Finite O (wpart O u j) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk g₁ hg₁ R _ _ _ u hu hfin
  classical
  obtain ⟨W, hW, -⟩ := exists_adapted F hOk g₁ hg₁ u hu
  have hpart : ∀ j, W.part j = wpart O u j := hW.part
  have hfg0 : (W.part 0).FG := by
    rw [hpart]
    exact Module.Finite.iff_fg.mp hfin
  have hadj : ∀ x ∈ W.part 0, x ∈ Algebra.adjoin O (Set.range W.z) := part_zero_le W hfg0
  let E : Set R := {x | ∃ g a b, F.η g = 1 ∧ x = (u g).mat a b}
  have hzE : Algebra.adjoin O (Set.range W.z) ≤ Algebra.adjoin O E := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, a, b, hg, -, hz⟩ := hW.var i
    rw [hz]
    apply Subalgebra.sub_mem
    · exact Algebra.subset_adjoin ⟨g, a, b, hg, rfl⟩
    · rw [Frame.rz.eq_1, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply]
      exact Subalgebra.algebraMap_mem _ _
  have hpartj : ∀ j, ∀ x ∈ W.part j, x ∈ Algebra.adjoin O E := by
    intro j x hx
    obtain ⟨B, hB⟩ := part_decomp W j
    rw [hB] at hx
    have hle : (⨆ b ∈ B, (W.part 0).map (LinearMap.mulLeft O (W.π (MvPowerSeries.monomial b 1)))) ≤
        Subalgebra.toSubmodule (Algebra.adjoin O E) := by
      refine iSup₂_le fun b _ => ?_
      rintro _ ⟨y, hy, rfl⟩
      exact Subalgebra.mul_mem _ (hzE (monomial_mem_adjoin W b)) (hzE (hadj y hy))
    exact hle hx
  refine ⟨?_, fun j => ?_⟩
  · apply le_antisymm
    · intro x hx
      rw [Sring.eq_1, gradedSub.eq_1] at hx
      have hx' : x ∈ ⨆ j, wpart O u j := hx
      have hle : (⨆ j, wpart O u j) ≤ Subalgebra.toSubmodule (Algebra.adjoin O E) := by
        refine iSup_le fun j => ?_
        intro y hy
        rw [← hpart] at hy
        exact hpartj j y hy
      exact hle hx'
    · apply Algebra.adjoin_le
      rintro _ ⟨g, a, b, _, rfl⟩
      exact mem_Sring u (entry_mem u g a b)
  · rw [← hpart]
    obtain ⟨B, hB⟩ := part_decomp W j
    rw [Module.Finite.iff_fg, hB]
    exact Submodule.fg_biSup B _ (fun b _ => hfg0.map _)
