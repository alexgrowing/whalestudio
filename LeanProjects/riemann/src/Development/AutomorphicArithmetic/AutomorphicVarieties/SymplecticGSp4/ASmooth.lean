import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section PartA
open MvPowerSeries

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]

private lemma exists_order {X : Type} [AddCommGroup X] (W : WPres O X R) (h : W.HasOrigin) (n : ℕ) :
    ∀ x ∈ RingHom.ker (W.origin h) ^ n, ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order := by
  induction n with
  | zero =>
    intro x _
    obtain ⟨f, rfl⟩ := W.surj x
    exact ⟨f, rfl, by simp⟩
  | succ n ih =>
    let I : Ideal R :=
      { carrier := {x | ∃ f, W.π f = x ∧ ((n + 1 : ℕ) : ℕ∞) ≤ f.order}
        add_mem' := by
          rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
          exact ⟨f + g, map_add _ _ _, le_trans (le_min hf hg) MvPowerSeries.min_order_le_add⟩
        zero_mem' := ⟨0, map_zero _, by simp⟩
        smul_mem' := by
          rintro c _ ⟨f, rfl, hf⟩
          obtain ⟨g, rfl⟩ := W.surj c
          refine ⟨g * f, by rw [map_mul, smul_eq_mul], le_trans ?_ MvPowerSeries.le_order_mul⟩
          exact le_trans hf le_add_self }
    have hle : RingHom.ker (W.origin h) ^ (n + 1) ≤ I := by
      rw [pow_succ]
      refine Ideal.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨f, rfl, hf⟩ := ih a ha
      obtain ⟨g, rfl⟩ := W.surj b
      have hg : ((1 : ℕ) : ℕ∞) ≤ g.order := by
        refine MvPowerSeries.nat_le_order fun d hd => ?_
        have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
        subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        rwa [RingHom.mem_ker, WPres.origin_π] at hb
      refine ⟨f * g, map_mul _ _ _, le_trans ?_ MvPowerSeries.le_order_mul⟩
      rw [Nat.cast_add]
      exact add_le_add hf hg
    exact fun x hx => hle hx

private lemma monomial_mem {X : Type} [AddCommGroup X] {σ : Type} (wt : σ → X) (m : σ →₀ ℕ) (c : O) :
    monomial m c ∈ wtPart O wt (Finsupp.weight wt m) := fun k hk => by
  classical
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hk rfl

private lemma mem_A (W : WPres O (ℤ × ℤ) R) {A : Subalgebra O R} (hA : ∀ f, f ∈ A ↔ f ∈ ⨆ n : ℤ, W.part (0, n))
    {j : ℤ × ℤ} (hj : j.1 = 0) {f : R} (hf : f ∈ W.part j) : f ∈ A := by
  rw [hA]
  obtain ⟨j1, j2⟩ := j
  dsimp only at hj
  subst hj
  exact Submodule.mem_iSup_of_mem j2 hf

private theorem wcomp_eq_self_of_mem_wtPart {σ X : Type} [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_of_ne_eq_zero_of_mem_wtPart {σ X : Type} [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private lemma A_sum (W : WPres O (ℤ × ℤ) R) {A : Subalgebra O R} (hA : ∀ f, f ∈ A ↔ f ∈ ⨆ n : ℤ, W.part (0, n))
    (g : MvPowerSeries W.σ O) (hx : W.π g ∈ A) :
    ∃ T : Finset (ℤ × ℤ), (∀ j ∈ T, j.1 = 0) ∧ W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) := by
  classical
  have key : ∀ y ∈ (⨆ n : ℤ, W.part (0, n)), ∃ T : Finset (ℤ × ℤ), (∀ j ∈ T, j.1 = 0) ∧
      ∀ g, W.π g = y → W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) ∧
        ∀ j ∉ T, W.π (wcomp O W.wt j g) = 0 := by
    intro y hy
    refine Submodule.iSup_induction' (fun n : ℤ => W.part (0, n))
      (motive := fun y _ => ∃ T : Finset (ℤ × ℤ), (∀ j ∈ T, j.1 = 0) ∧
        ∀ g, W.π g = y → W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) ∧
          ∀ j ∉ T, W.π (wcomp O W.wt j g) = 0) ?_ ?_ ?_ hy
    · intro n y hy
      obtain ⟨f, hf, rfl⟩ := hy
      refine ⟨{(0, n)}, by simp, fun g hg => ?_⟩
      change W.π g = W.π f at hg
      have hker : ∀ j, W.π (wcomp O W.wt j g) = W.π (wcomp O W.wt j f) := by
        intro j
        have hm : g - f ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hg, sub_self]
        have := W.homog _ hm j
        rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at this
        exact this
      refine ⟨?_, fun j hj => ?_⟩
      · rw [Finset.sum_singleton, hker, wcomp_eq_self_of_mem_wtPart hf, hg]
      · rw [hker, wcomp_of_ne_eq_zero_of_mem_wtPart hf (by simpa using hj), map_zero]
    · refine ⟨∅, by simp, fun g hg => ⟨by simpa using hg, fun j _ => ?_⟩⟩
      exact W.homog _ (show g ∈ RingHom.ker W.π from hg) j
    · intro y1 y2 _ _ ih1 ih2
      obtain ⟨T1, hT1, h1⟩ := ih1
      obtain ⟨T2, hT2, h2⟩ := ih2
      refine ⟨T1 ∪ T2, fun j hj => ?_, fun g hg => ?_⟩
      · rcases Finset.mem_union.mp hj with hj | hj
        exacts [hT1 j hj, hT2 j hj]
      obtain ⟨g1, hg1⟩ := W.surj y1
      have hg2 : W.π (g - g1) = y2 := by rw [map_sub, hg, hg1, add_sub_cancel_left]
      obtain ⟨e1, z1⟩ := h1 g1 hg1
      obtain ⟨e2, z2⟩ := h2 (g - g1) hg2
      have hsplit : ∀ j, W.π (wcomp O W.wt j g) =
          W.π (wcomp O W.wt j g1) + W.π (wcomp O W.wt j (g - g1)) := by
        intro j
        rw [← map_add, ← map_add, add_sub_cancel]
      refine ⟨?_, fun j hj => ?_⟩
      · rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
          ← Finset.sum_subset Finset.subset_union_left (fun j _ hj => z1 j hj),
          ← Finset.sum_subset Finset.subset_union_right (fun j _ hj => z2 j hj), ← e1, ← e2, ← map_add,
          add_sub_cancel]
      · rw [Finset.mem_union, not_or] at hj
        rw [hsplit, z1 j hj.1, z2 j hj.2, add_zero]
  obtain ⟨T, hT, h⟩ := key _ ((hA _).mp hx)
  exact ⟨T, hT, (h g rfl).1⟩

private lemma org_mono {X : Type} [AddCommGroup X] (W : WPres O X R) (h : W.HasOrigin) {m : W.σ →₀ ℕ} (hm : m ≠ 0) :
    W.origin h (W.π (monomial m 1)) = 0 := by
  classical
  rw [W.origin_π, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hm.symm]

private lemma pow_le (W : WPres O (ℤ × ℤ) R) (h : W.HasOrigin) {A : Subalgebra O R}
    (hA : ∀ f, f ∈ A ↔ f ∈ ⨆ n : ℤ, W.part (0, n)) (N : Submodule O R)
    (hN : ∀ a ∈ A, ∀ b ∈ A, W.origin h a = 0 → W.origin h b = 0 → a * b ∈ N) (k : ℕ) (hk : 1 ≤ k)
    (hz : ∀ m, (Finsupp.weight W.wt m).1 = 0 → k ≤ m.degree → W.π (monomial m 1) ∈ N) :
    ∀ y ∈ A, y ∈ RingHom.ker (W.origin h) ^ k → y ∈ N := by
  classical
  intro y hyA hyk
  obtain ⟨f, rfl, hf⟩ := exists_order W h k y hyk
  obtain ⟨T, hT, hsum⟩ := A_sum W hA f hyA
  rw [hsum]
  refine Submodule.sum_mem _ fun j hj => ?_
  obtain ⟨μ, hμS, hμ⟩ := part_span O R (ℤ × ℤ) W {n | Finsupp.weight W.wt n = j ∧ k ≤ n.degree} j
    (fun n hn => hn.1)
  have hsupp : ∀ n ∉ {n : W.σ →₀ ℕ | Finsupp.weight W.wt n = j ∧ k ≤ n.degree},
      MvPowerSeries.coeff n (wcomp O W.wt j f) = 0 := by
    intro n hn
    rw [coeff_wcomp]
    split_ifs with hw
    · apply MvPowerSeries.coeff_of_lt_order
      have hlt : n.degree < k := by
        by_contra hc
        exact hn ⟨hw, not_lt.mp hc⟩
      exact lt_of_lt_of_le (by exact_mod_cast hlt) hf
    · rfl
  obtain ⟨b, hb, hbe⟩ := hμ (wcomp O W.wt j f) hsupp
  rw [hbe, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmS := hμS hm
  have hmpart : W.π (monomial m 1) ∈ W.part j := by
    rw [← hmS.1]
    exact ⟨_, monomial_mem W.wt m 1, rfl⟩
  have hmA : W.π (monomial m 1) ∈ A := mem_A W hA (hT j hj) hmpart
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hmS.2
    simp at this
    omega
  have hmker : W.origin h (W.π (monomial m 1)) = 0 := org_mono W h hm0
  have hmN : W.π (monomial m 1) ∈ N := hz m (by rw [hmS.1]; exact hT j hj) hmS.2
  have hbA : W.π (b m) ∈ A := mem_A W hA (j := 0) rfl ⟨b m, hb m, rfl⟩
  rw [map_mul]
  have hsplit : W.π (b m) * W.π (monomial m 1) =
      (W.origin h (W.π (b m))) • W.π (monomial m 1) +
        (W.π (b m) - algebraMap O R (W.origin h (W.π (b m)))) * W.π (monomial m 1) := by
    rw [sub_mul, Algebra.smul_def]
    ring
  rw [hsplit]
  refine add_mem (N.smul_mem _ hmN) (hN _ (sub_mem hbA (A.algebraMap_mem _)) _ hmA ?_ hmker)
  rw [map_sub, AlgHom.commutes]
  simp

private lemma split_mono {σ : Type} (wt : σ → ℤ × ℤ) (hw : ∀ i, (wt i).1 = -1 ∨ (wt i).1 = 0 ∨ (wt i).1 = 1)
    (m : σ →₀ ℕ) (hm : m ≠ 0) (h0 : (Finsupp.weight wt m).1 = 0) :
    (∃ s m', (wt s).1 = 0 ∧ m = Finsupp.single s 1 + m') ∨
      ∃ s t m', (wt s).1 = 1 ∧ (wt t).1 = -1 ∧ m = Finsupp.single s 1 + Finsupp.single t 1 + m' := by
  classical
  by_cases h0' : ∃ s, m s ≠ 0 ∧ (wt s).1 = 0
  · obtain ⟨s, hs, hs0⟩ := h0'
    left
    refine ⟨s, m - Finsupp.single s 1, hs0, ?_⟩
    rw [add_tsub_cancel_of_le]
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hs
  · push_neg at h0'
    right
    have hsum : ∑ i ∈ m.support, (m i : ℤ) * (wt i).1 = 0 := by
      have := h0
      rw [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum] at this
      simpa [nsmul_eq_mul] using this
    have hne := Finsupp.support_nonempty_iff.mpr hm
    have hpm : ∀ i ∈ m.support, (wt i).1 = 1 ∨ (wt i).1 = -1 := by
      intro i hi
      have := h0' i (Finsupp.mem_support_iff.mp hi)
      rcases hw i with h | h | h
      · exact Or.inr h
      · exact absurd h this
      · exact Or.inl h
    obtain ⟨s, hs, hs1⟩ : ∃ s ∈ m.support, (wt s).1 = 1 := by
      by_contra hc
      push_neg at hc
      have hlt : ∑ i ∈ m.support, (m i : ℤ) * (wt i).1 < 0 := by
        refine Finset.sum_neg (fun i hi => ?_) hne
        rcases hpm i hi with h | h
        · exact absurd h (hc i hi)
        · rw [h]
          have hmi : (0 : ℤ) < m i := by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
          linarith
      linarith
    obtain ⟨t, ht, ht1⟩ : ∃ t ∈ m.support, (wt t).1 = -1 := by
      by_contra hc
      push_neg at hc
      have hlt : 0 < ∑ i ∈ m.support, (m i : ℤ) * (wt i).1 := by
        refine Finset.sum_pos (fun i hi => ?_) hne
        rcases hpm i hi with h | h
        · rw [h]
          have hmi : (0 : ℤ) < m i := by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
          linarith
        · exact absurd h (hc i hi)
      linarith
    have hst : s ≠ t := by
      rintro rfl
      rw [hs1] at ht1
      norm_num at ht1
    refine ⟨s, t, m - (Finsupp.single s 1 + Finsupp.single t 1), hs1, ht1, ?_⟩
    rw [add_tsub_cancel_of_le]
    rw [Finsupp.le_def]
    intro i
    have hs' := Finsupp.mem_support_iff.mp hs
    have ht' := Finsupp.mem_support_iff.mp ht
    by_cases his : i = s
    · subst his
      simp [Finsupp.single_apply, hst, Ne.symm hst] <;> omega
    · by_cases hit : i = t
      · subst hit
        simp [Finsupp.single_apply, hst, Ne.symm hst] <;> omega
      · simp [Finsupp.single_apply, Ne.symm his, Ne.symm hit]

private lemma ker_le (W : WPres O (ℤ × ℤ) R) (h : W.HasOrigin)
    (hw : ∀ i, (W.wt i).1 = -1 ∨ (W.wt i).1 = 0 ∨ (W.wt i).1 = 1) {A : Subalgebra O R}
    (hA : ∀ f, f ∈ A ↔ f ∈ ⨆ n : ℤ, W.part (0, n)) (N : Submodule O R)
    (hN : ∀ a ∈ A, ∀ b ∈ A, W.origin h a = 0 → W.origin h b = 0 → a * b ∈ N)
    (hsat : ∀ c : O, c ≠ 0 → ∀ f, c • f ∈ N → f ∈ N)
    (h1 : ∀ s, (W.wt s).1 = 0 → ∃ c : O, c ≠ 0 ∧ ∃ g ∈ N, g ∈ A ∧ c • W.z s - g ∈ RingHom.ker (W.origin h) ^ 2)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 →
      ∃ c : O, c ≠ 0 ∧ ∃ g ∈ N, g ∈ A ∧ c • (W.z s * W.z t) - g ∈ RingHom.ker (W.origin h) ^ 3) :
    ∀ y ∈ A, W.origin h y = 0 → y ∈ N := by
  classical
  have wsingle : ∀ s, Finsupp.weight W.wt (Finsupp.single s 1) = W.wt s := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  have monoA : ∀ m : W.σ →₀ ℕ, (Finsupp.weight W.wt m).1 = 0 → W.π (monomial m 1) ∈ A := by
    intro m hm
    exact mem_A W hA hm ⟨_, monomial_mem W.wt m 1, rfl⟩
  have monoMul : ∀ a b : W.σ →₀ ℕ, W.π (monomial (a + b) (1 : O)) =
      W.π (monomial a 1) * W.π (monomial b 1) := by
    intro a b
    rw [← map_mul, MvPowerSeries.monomial_mul_monomial, mul_one]
  have zeq : ∀ s, W.z s = W.π (monomial (Finsupp.single s 1) 1) := fun s => rfl
  have prodN : ∀ a b : W.σ →₀ ℕ, a ≠ 0 → b ≠ 0 → (Finsupp.weight W.wt a).1 = 0 →
      (Finsupp.weight W.wt b).1 = 0 → W.π (monomial (a + b) 1) ∈ N := by
    intro a b ha hb hwa hwb
    rw [monoMul]
    exact hN _ (monoA a hwa) _ (monoA b hwb) (org_mono W h ha) (org_mono W h hb)
  have degAdd : ∀ a b : W.σ →₀ ℕ, (a + b).degree = a.degree + b.degree := fun a b => map_add _ a b
  have wtAdd : ∀ a b : W.σ →₀ ℕ, (Finsupp.weight W.wt (a + b)).1 =
      (Finsupp.weight W.wt a).1 + (Finsupp.weight W.wt b).1 := by
    intro a b
    rw [map_add, Prod.fst_add]
  have ne0 : ∀ a : W.σ →₀ ℕ, 1 ≤ a.degree → a ≠ 0 := by
    rintro a ha rfl
    simp at ha
  have sne : ∀ s : W.σ, Finsupp.single s 1 ≠ 0 := fun s => Finsupp.single_ne_zero.mpr one_ne_zero
  have hz3 : ∀ m : W.σ →₀ ℕ, (Finsupp.weight W.wt m).1 = 0 → 3 ≤ m.degree → W.π (monomial m 1) ∈ N := by
    intro m h0 hd
    rcases split_mono W.wt hw m (ne0 m (by omega)) h0 with ⟨s, m', hs, rfl⟩ | ⟨s, t, m', hs, ht, rfl⟩
    · rw [degAdd, Finsupp.degree_single] at hd
      rw [wtAdd, wsingle, hs, zero_add] at h0
      exact prodN _ _ (sne s) (ne0 m' (by omega)) (by rw [wsingle, hs]) h0
    · rw [degAdd, degAdd, Finsupp.degree_single, Finsupp.degree_single] at hd
      rw [wtAdd, wtAdd, wsingle, wsingle, hs, ht] at h0
      refine prodN _ _ ?_ (ne0 m' (by omega)) ?_ (by omega)
      · exact ne0 _ (by rw [degAdd, Finsupp.degree_single]; omega)
      · rw [wtAdd, wsingle, wsingle, hs, ht]
        norm_num
  have hA3 := pow_le W h hA N hN 3 (by norm_num) hz3
  have hz2 : ∀ m : W.σ →₀ ℕ, (Finsupp.weight W.wt m).1 = 0 → 2 ≤ m.degree → W.π (monomial m 1) ∈ N := by
    intro m h0 hd
    rcases split_mono W.wt hw m (ne0 m (by omega)) h0 with ⟨s, m', hs, rfl⟩ | ⟨s, t, m', hs, ht, rfl⟩
    · rw [degAdd, Finsupp.degree_single] at hd
      rw [wtAdd, wsingle, hs, zero_add] at h0
      exact prodN _ _ (sne s) (ne0 m' (by omega)) (by rw [wsingle, hs]) h0
    · have h0' := h0
      rw [wtAdd, wtAdd, wsingle, wsingle, hs, ht] at h0'
      by_cases hm' : m' = 0
      · subst hm'
        rw [add_zero, monoMul, ← zeq, ← zeq]
        obtain ⟨c, hc, g, hgN, hgA, hg⟩ := h2 s t hs ht
        have hzA : W.z s * W.z t ∈ A := by
          rw [zeq, zeq, ← monoMul]
          exact monoA _ (by rw [wtAdd, wsingle, wsingle, hs, ht]; norm_num)
        have hmem : c • (W.z s * W.z t) - g ∈ N :=
          hA3 _ (sub_mem (A.smul_mem hzA c) hgA) hg
        refine hsat c hc _ ?_
        have := add_mem hmem hgN
        rwa [sub_add_cancel] at this
      · refine prodN _ _ ?_ hm' ?_ (by omega)
        · exact ne0 _ (by rw [degAdd, Finsupp.degree_single]; omega)
        · rw [wtAdd, wsingle, wsingle, hs, ht]
          norm_num
  have hA2 := pow_le W h hA N hN 2 (by norm_num) hz2
  have hz1 : ∀ m : W.σ →₀ ℕ, (Finsupp.weight W.wt m).1 = 0 → 1 ≤ m.degree → W.π (monomial m 1) ∈ N := by
    intro m h0 hd
    by_cases hd2 : 2 ≤ m.degree
    · exact hz2 m h0 hd2
    rcases split_mono W.wt hw m (ne0 m hd) h0 with ⟨s, m', hs, rfl⟩ | ⟨s, t, m', hs, ht, rfl⟩
    · rw [degAdd, Finsupp.degree_single] at hd2
      have hm' : m' = 0 := (Finsupp.degree_eq_zero_iff m').mp (by omega)
      subst hm'
      rw [add_zero, ← zeq]
      obtain ⟨c, hc, g, hgN, hgA, hg⟩ := h1 s hs
      have hzA : W.z s ∈ A := by
        rw [zeq]
        exact monoA _ (by rw [wsingle, hs])
      have hmem : c • W.z s - g ∈ N := hA2 _ (sub_mem (A.smul_mem hzA c) hgA) hg
      refine hsat c hc _ ?_
      have := add_mem hmem hgN
      rwa [sub_add_cancel] at this
    · rw [degAdd, degAdd, Finsupp.degree_single, Finsupp.degree_single] at hd2
      omega
  have hA1 := pow_le W h hA N hN 1 le_rfl hz1
  intro y hy hy0
  exact hA1 y hy (by rw [pow_one]; exact hy0)

end PartA

section PartB
open MvPowerSeries

variable {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
  {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private noncomputable def crLin (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem crLin_apply (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    crLin φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem coeff_single_one_mul_eq_zero_of_constantCoeff_zero {E κ : Type} [CommRing E] (p q : MvPowerSeries κ E) (i : κ)
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) : coeff (Finsupp.single i 1) (p * q) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun y hy => ?_
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have hd : y.1.degree + y.2.degree = 1 := by
    rw [← map_add, hy', Finsupp.degree_single]
  rcases Nat.eq_zero_or_pos y.1.degree with h0 | h0
  · rw [(Finsupp.degree_eq_zero_iff _).mp h0, coeff_zero_eq_constantCoeff_apply, hp, zero_mul]
  · have h1 : y.2.degree = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp h1, coeff_zero_eq_constantCoeff_apply, hq, mul_zero]

private theorem crLin_sq (h : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)) (i : τ) :
    ∀ f ∈ RingHom.ker x ^ 2, crLin φ i f = 0 := by
  intro f hf
  rw [sq] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    have ha' : constantCoeff (φ a) = 0 := by rw [h, RingHom.mem_ker.mp ha, map_zero]
    have hb' : constantCoeff (φ b) = 0 := by rw [h, RingHom.mem_ker.mp hb, map_zero]
    rw [crLin_apply, map_mul]
    exact coeff_single_one_mul_eq_zero_of_constantCoeff_zero _ _ i ha' hb'
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

private theorem crLin_wt (h : IsChart 𝒜 x wt φ) (i : τ) {j : X} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : crLin φ i f = 0 := by
  have h' : ∀ n, Finsupp.weight wt n ≠ j → coeff n (φ f) = 0 := h.graded j f hf
  rw [crLin_apply]
  apply h'
  rw [Finsupp.weight_single, one_smul]
  exact hij

private theorem crLin_const (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (c : O) :
    crLin φ i (algebraMap O A c) = 0 := by
  classical
  rw [crLin_apply, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C,
    if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]

private theorem cr_fixed (h : IsChart 𝒜 x wt φ) {j : X} (hj : j ≠ 0) {f : A} (hf : f ∈ 𝒜 j) : x f = 0 := by
  have h1' : ∀ n, Finsupp.weight wt n ≠ j → coeff n (φ f) = 0 := h.graded j f hf
  have h2 := h.const f
  rw [← coeff_zero_eq_constantCoeff_apply, h1' 0 (by rw [map_zero]; exact fun e => hj e.symm)] at h2
  exact (IsFractionRing.injective O (FractionRing O)) (h2.symm.trans (map_zero _).symm)

private theorem crLin_proj [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (i : τ) {j : X}
    (hij : wt i = j) (f : A) : crLin φ i (DirectSum.decompose 𝒜 f j) = crLin φ i f := by
  classical
  symm
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  rw [map_sum]
  refine Finset.sum_eq_single j
    (fun j' _ hj' => crLin_wt h i (by rw [hij]; exact fun e => hj' e.symm) (SetLike.coe_mem _)) ?_
  intro hj
  rw [DFinsupp.notMem_support_iff.mp hj]
  simp

private theorem cr_comp [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (j : X) (f : A) :
    ∃ g : A, g ∈ 𝒜 j ∧ x g = 0 ∧ ∀ i, wt i = j → crLin φ i g = crLin φ i f := by
  classical
  by_cases hj : j = 0
  · subst hj
    refine ⟨(DirectSum.decompose 𝒜 f 0 : A) - algebraMap O A (x (DirectSum.decompose 𝒜 f 0)), ?_, ?_, ?_⟩
    · exact sub_mem (SetLike.coe_mem _) (SetLike.algebraMap_mem_graded 𝒜 _)
    · simp
    · intro i hi
      rw [map_sub, crLin_const, sub_zero, crLin_proj h i hi]
  · exact ⟨DirectSum.decompose 𝒜 f j, SetLike.coe_mem _, cr_fixed h hj (SetLike.coe_mem _),
      fun i hi => crLin_proj h i hi f⟩

private theorem homog_gens [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) :
    ∃ g : τ → A, ∀ i, g i ∈ 𝒜 (wt i) ∧ x (g i) = 0 ∧ crLin φ i (g i) ≠ 0 ∧ ∀ i', i' ≠ i → crLin φ i' (g i) = 0 := by
  classical
  choose f hf1 hf2 using h.onto
  refine ⟨fun i => (cr_comp h (wt i) (f i)).choose, fun i => ?_⟩
  obtain ⟨hg1, hg2, hg3⟩ := (cr_comp h (wt i) (f i)).choose_spec
  refine ⟨hg1, hg2, ?_, fun i' hi' => ?_⟩
  · rw [hg3 i rfl, crLin_apply]
    exact hf1 i
  · by_cases hw : wt i' = wt i
    · rw [hg3 i' hw, crLin_apply]
      exact hf2 i i' hi'
    · exact crLin_wt h i' hw hg1

private theorem clear_den [Fintype τ] (u : τ → FractionRing O) :
    ∃ c : O, c ≠ 0 ∧ ∃ a : τ → O, ∀ k, algebraMap O (FractionRing O) (a k) = c • u k := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) u
  have hb' : ∀ k, ∃ a : O, algebraMap O (FractionRing O) a = (b : O) • u k := fun k => hb k
  choose a ha using hb'
  exact ⟨b, nonZeroDivisors.ne_zero b.2, a, ha⟩

private theorem expand [Fintype τ] (h : IsChart 𝒜 x wt φ) {g : τ → A}
    (hg : ∀ i, g i ∈ 𝒜 (wt i) ∧ x (g i) = 0 ∧ crLin φ i (g i) ≠ 0 ∧ ∀ i', i' ≠ i → crLin φ i' (g i) = 0)
    {j : X} {p : A} (hp : p ∈ 𝒜 j) (hp0 : x p = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ a : τ → O, (∀ k, wt k ≠ j → a k = 0) ∧ c • p - ∑ k, a k • g k ∈ RingHom.ker x ^ 2 := by
  classical
  obtain ⟨c, hc, a, ha⟩ := clear_den (fun k => if wt k = j then crLin φ k p / crLin φ k (g k) else 0)
  have ha0 : ∀ k, wt k ≠ j → a k = 0 := by
    intro k hk
    have := ha k
    rw [if_neg hk, smul_zero] at this
    exact IsFractionRing.injective O (FractionRing O) (this.trans (map_zero _).symm)
  have hxq : x (c • p - ∑ k, a k • g k) = 0 := by
    rw [map_sub, map_sum, map_smul, hp0, smul_zero, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun k _ => by rw [map_smul, (hg k).2.1, smul_zero]
  have hcr : ∀ i, coeff (Finsupp.single i 1) (φ (c • p - ∑ k, a k • g k)) = 0 := by
    intro i
    rw [← crLin_apply, map_sub, map_sum, map_smul,
      Finset.sum_eq_single i (fun k _ hk => by rw [map_smul, (hg k).2.2.2 i (fun e => hk e.symm), smul_zero])
        (fun hi => absurd (Finset.mem_univ i) hi), map_smul]
    by_cases hi : wt i = j
    · have := ha i
      rw [if_pos hi] at this
      rw [Algebra.smul_def (a i), this, smul_mul_assoc, div_mul_cancel₀ _ (hg i).2.2.1, sub_self]
    · rw [crLin_wt h i hi hp, ha0 i hi, smul_zero, zero_smul, sub_self]
  obtain ⟨c', hc', hq2⟩ := h.inj _ hxq hcr
  refine ⟨c' * c, mul_ne_zero hc' hc, fun k => c' * a k, fun k hk => show c' * a k = 0 by rw [ha0 k hk, mul_zero], ?_⟩
  convert hq2 using 1
  rw [smul_sub, Finset.smul_sum, mul_smul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [mul_smul]

private theorem chart_of_span [Fintype τ] (h1 : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j)
    (h2 : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)) (G : τ → A)
    (hinj : ∀ v : τ → FractionRing O, (∀ j, ∑ k, v k * crLin φ j (G k) = 0) → v = 0)
    (hspan : ∀ f, x f = 0 → ∃ c : O, c ≠ 0 ∧ ∃ a : τ → O, c • f - ∑ k, a k • G k ∈ RingHom.ker x ^ 2) :
    IsChart 𝒜 x wt φ := by
  classical
  refine ⟨h1, h2, ?_, ?_⟩
  · intro i
    let Mx : Matrix τ τ (FractionRing O) := fun j k => crLin φ j (G k)
    have hinj' : Function.Injective Mx.mulVec := by
      intro v w hvw
      have hvw' : v - w = 0 := hinj (v - w) (fun j => by
        have e := congrFun hvw j
        simp only [Matrix.mulVec, dotProduct] at e
        rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
        rw [← e]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Mx, Pi.sub_apply]
        ring)
      exact sub_eq_zero.mp hvw'
    have hsurj : Function.Surjective Mx.mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj')
    obtain ⟨v, hv⟩ := hsurj (Pi.single i 1)
    obtain ⟨c, hc, a, ha⟩ := clear_den v
    have key : ∀ j, coeff (Finsupp.single j 1) (φ (∑ k, a k • G k)) = c • (Pi.single i 1 : τ → FractionRing O) j := by
      intro j
      rw [← crLin_apply, map_sum]
      have e := congrFun hv j
      simp only [Matrix.mulVec, dotProduct] at e
      rw [← e, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Algebra.smul_def (a k), ha k]
      simp only [Algebra.smul_def, Mx]
      ring
    refine ⟨∑ k, a k • G k, ?_, fun i' hi' => ?_⟩
    · rw [key, Pi.single_eq_same, Algebra.smul_def, mul_one]
      exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc
    · rw [key, Pi.single_eq_of_ne hi', smul_zero]
  · intro f hf hcr
    obtain ⟨c, hc, a, hsq⟩ := hspan f hf
    have ha : (fun k => algebraMap O (FractionRing O) (a k)) = 0 := hinj _ (fun j => by
      have e := crLin_sq h2 j _ hsq
      rw [map_sub, map_smul, crLin_apply, hcr j, smul_zero, zero_sub, neg_eq_zero, map_sum] at e
      rw [← e]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Algebra.smul_def])
    have ha' : ∀ k, a k = 0 := fun k =>
      IsFractionRing.injective O (FractionRing O) ((congrFun ha k).trans (map_zero _).symm)
    exact ⟨c, hc, by simpa [ha'] using hsq⟩

omit [IsDomain O] in
private theorem restrict {E τ' : Type} [CommRing E] [Algebra O E] (φ : A →ₐ[O] MvPowerSeries τ E)
    (ι : (τ' →₀ ℕ) →+ (τ →₀ ℕ)) (hι : Function.Injective ι)
    (hφ : ∀ f m, m ∉ Set.range ι → coeff m (φ f) = 0) :
    ∃ ψ : A →ₐ[O] MvPowerSeries τ' E, ∀ f n, coeff n (ψ f) = coeff (ι n) (φ f) := by
  classical
  have hmap : ∀ f g : A, ∀ n, coeff (ι n) (φ f * φ g) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff (ι p.1) (φ f) * coeff (ι p.2) (φ g) := by
    intro f g n
    rw [coeff_mul]
    symm
    have e : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff (ι p.1) (φ f) * coeff (ι p.2) (φ g) =
        ∑ q ∈ (Finset.HasAntidiagonal.antidiagonal n).map (Function.Embedding.prodMap ⟨ι, hι⟩ ⟨ι, hι⟩),
          coeff q.1 (φ f) * coeff q.2 (φ g) := by
      rw [Finset.sum_map]
      rfl
    rw [e]
    apply Finset.sum_subset
    · intro q hq
      rw [Finset.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd]
      rw [← map_add, hp]
    · intro q hq hq'
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      by_cases hq1 : q.1 ∈ Set.range ι
      · by_cases hq2 : q.2 ∈ Set.range ι
        · exfalso
          obtain ⟨a, ha⟩ := hq1
          obtain ⟨b, hb⟩ := hq2
          apply hq'
          rw [Finset.mem_map]
          refine ⟨(a, b), ?_, ?_⟩
          · rw [Finset.HasAntidiagonal.mem_antidiagonal]
            apply hι
            rw [map_add, ha, hb, hq]
          · simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map, ha, hb]
        · rw [hφ g _ hq2, mul_zero]
      · rw [hφ f _ hq1, zero_mul]
  let L : A →ₗ[O] MvPowerSeries τ' E :=
    { toFun := fun f n => coeff (ι n) (φ f)
      map_add' := fun f g => by
        ext n
        change coeff (ι n) (φ (f + g)) = coeff (ι n) (φ f) + coeff (ι n) (φ g)
        rw [map_add, map_add]
      map_smul' := fun c f => by
        ext n
        change coeff (ι n) (φ (c • f)) = c • coeff (ι n) (φ f)
        rw [map_smul]
        rfl }
  refine ⟨AlgHom.ofLinearMap L ?_ ?_, fun f n => rfl⟩
  · ext n
    change coeff (ι n) (φ 1) = coeff n 1
    rw [map_one, coeff_one, coeff_one]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn, if_neg (fun e => hn (hι (e.trans (map_zero ι).symm)))]
  · intro f g
    ext n
    change coeff (ι n) (φ (f * g)) = coeff n (L f * L g)
    rw [map_mul, hmap, coeff_mul]
    rfl

private theorem exists_eq_single_one_of_degree_eq_one {κ : Type} {v : κ →₀ ℕ} (hv : v.degree = 1) : ∃ t, v = Finsupp.single t 1 := by
  classical
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.mp hv0
  have hle : Finsupp.single t 1 ≤ v := by
    intro s
    by_cases hs : s = t
    · subst hs
      rw [Finsupp.single_eq_same]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at ht
      omega
    · rw [Finsupp.single_eq_of_ne hs]
      exact Nat.zero_le _
  have hsum : v = Finsupp.single t 1 + (v - Finsupp.single t 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : (v - Finsupp.single t 1).degree = 0 := by
    have e := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, hv] at e
    omega
  refine ⟨t, ?_⟩
  rw [hsum, (Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero]

private theorem coeff_two {E : Type} [CommRing E] [IsDomain E] [DecidableEq τ] (p q : MvPowerSeries τ E) (k b j : τ)
    (hp0 : coeff 0 p = 0) (hq0 : coeff 0 q = 0) (hp : ∀ i, i ≠ k → coeff (Finsupp.single i 1) p = 0)
    (hq : ∀ i, i ≠ b → coeff (Finsupp.single i 1) q = 0) :
    coeff (Finsupp.single j 1 + Finsupp.single b 1) (p * q) =
      if j = k then coeff (Finsupp.single k 1) p * coeff (Finsupp.single b 1) q else 0 := by
  rw [coeff_mul, Finset.sum_eq_single (Finsupp.single j 1, Finsupp.single b 1)]
  · by_cases hjk : j = k
    · rw [if_pos hjk, hjk]
    · rw [if_neg hjk, hp j hjk, zero_mul]
  · intro y hy hne
    have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
    by_cases h1 : y.1 = 0
    · rw [h1, coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, hp0, zero_mul]
    by_cases h2 : y.2 = 0
    · rw [h2, coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, hq0, mul_zero]
    have hd : y.1.degree + y.2.degree = 2 := by
      rw [← map_add, hy', map_add, Finsupp.degree_single, Finsupp.degree_single]
    have hd1 : y.1.degree ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).mp e)
    have hd2 : y.2.degree ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).mp e)
    obtain ⟨t, ht⟩ := exists_eq_single_one_of_degree_eq_one (v := y.2) (by omega)
    have htb : t ≠ b := by
      rintro rfl
      apply hne
      have e1 : y.1 = Finsupp.single j 1 := by
        rw [ht] at hy'
        exact add_right_cancel hy'
      exact Prod.ext e1 ht
    rw [ht, hq t htb, mul_zero]
  · intro hmem
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal (A := τ →₀ ℕ) (n := Finsupp.single j 1 + Finsupp.single b 1)
      (a := (Finsupp.single j 1, Finsupp.single b 1)) |>.mpr rfl) hmem

end PartB

section PartC
open MvPowerSeries

private theorem iota {τ : Type} [Fintype τ] [DecidableEq τ] (wt : τ → ℤ × ℤ) (b : τ) (hb : (wt b).1 = -1)
    (hτ : ∀ i, i ≠ b → (wt i).1 = 0 ∨ (wt i).1 = 1) :
    ∃ ι : ({i // i ≠ b} →₀ ℕ) →+ (τ →₀ ℕ), Function.Injective ι ∧
      (∀ i, ι (Finsupp.single i 1) = Finsupp.single i.1 1 + if (wt i.1).1 = 1 then Finsupp.single b 1 else 0) ∧
      (∀ n, Finsupp.weight wt (ι n) =
        (0, Finsupp.weight (fun i : {i // i ≠ b} => (wt i.1).2 + (wt i.1).1 * (wt b).2) n)) ∧
      ∀ m, (Finsupp.weight wt m).1 = 0 → m ∈ Set.range ι := by
  classical
  let v : {i // i ≠ b} → (τ →₀ ℕ) := fun i =>
    Finsupp.single i.1 1 + if (wt i.1).1 = 1 then Finsupp.single b 1 else 0
  let ι : ({i // i ≠ b} →₀ ℕ) →+ (τ →₀ ℕ) := Finsupp.liftAddHom fun i => multiplesHom (τ →₀ ℕ) (v i)
  have hιsk : ∀ i k, ι (Finsupp.single i k) = k • v i := fun i k => by
    simp only [ι, Finsupp.liftAddHom_apply_single, multiplesHom_apply]
  have hιapp : ∀ n t, ι n t =
      if h : t = b then ∑ i, (if (wt i.1).1 = 1 then n i else 0) else n ⟨t, h⟩ := by
    intro n t
    induction n using Finsupp.induction_linear with
    | zero =>
      simp
    | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg]
      split_ifs
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      · rfl
    | single i k =>
      rw [hιsk, Finsupp.smul_apply, smul_eq_mul]
      have hib : i.1 ≠ b := i.2
      by_cases ht : t = b
      · rw [dif_pos ht, Finset.sum_eq_single i]
        · by_cases h1 : (wt i.1).1 = 1
          · simp [v, h1, Finsupp.single_apply, hib, ht]
          · simp [v, h1, Finsupp.single_apply, hib, ht]
        · intro j _ hj
          simp [Finsupp.single_apply, Ne.symm hj]
        · simp
      · rw [dif_neg ht]
        by_cases h1 : (wt i.1).1 = 1
        · simp [v, h1, Finsupp.single_apply, Ne.symm ht, Subtype.ext_iff]
        · simp [v, h1, Finsupp.single_apply, Subtype.ext_iff]
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  · intro n n' h
    ext i
    have := congrArg (fun f : τ →₀ ℕ => f i.1) h
    simp only [hιapp, dif_neg i.2] at this
    exact this
  · intro i
    rw [hιsk, one_smul]
  · intro n
    have hw : (Finsupp.weight wt).comp ι =
        (AddMonoidHom.inr ℤ ℤ).comp (Finsupp.weight fun i : {i // i ≠ b} => (wt i.1).2 + (wt i.1).1 * (wt b).2) := by
      ext i
      all_goals
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply, hιsk, one_smul,
          Finsupp.weight_single, AddMonoidHom.inr_apply, v, map_add]
        rcases hτ i.1 i.2 with h | h <;> simp [h, hb, Finsupp.weight_single]
    exact DFunLike.congr_fun hw n
  · intro m hm
    refine ⟨Finsupp.equivFunOnFinite.symm fun i => m i.1, ?_⟩
    ext t
    rw [hιapp]
    split_ifs with h
    · subst h
      rw [Finsupp.weight_eq_sum, Fintype.sum_eq_add_sum_subtype_ne _ t] at hm
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, smul_eq_mul, hb] at hm
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      have key : ∑ x : {i // i ≠ t}, m x.1 • (wt x.1).1 =
          ((∑ x : {i // i ≠ t}, if (wt x.1).1 = 1 then m x.1 else 0 : ℕ) : ℤ) := by
        push_cast
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases hτ x.1 x.2 with h | h <;> simp [h]
      rw [key, nsmul_eq_mul, mul_neg_one] at hm
      omega
    · simp

private theorem exists_ne_zero_smul_mem_of_mem_span' {τ E : Type} [CommRing E] (p q : MvPowerSeries τ E)
    (hp : MvPowerSeries.coeff 0 p = 0) (hq : MvPowerSeries.coeff 0 q = 0) (j : τ) :
    MvPowerSeries.coeff (Finsupp.single j 1) (p * q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨x, y⟩ hxy
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
  have hx : ∀ i, x i + y i = (Finsupp.single j 1 : τ →₀ ℕ) i := fun i => by
    rw [← Finsupp.add_apply, hxy]
  rcases Nat.eq_zero_or_pos (x j) with h | h
  · have : x = 0 := by
      ext i
      by_cases hi : i = j
      · subst hi
        exact h
      · have := hx i
        simp only [Finsupp.single_apply] at this
        rw [if_neg (Ne.symm hi)] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
    subst this
    simp [hp]
  · have : y = 0 := by
      ext i
      have := hx i
      simp only [Finsupp.single_apply] at this
      by_cases hi : i = j
      · subst hi
        simp only [if_true] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
      · rw [if_neg (Ne.symm hi)] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
    subst this
    simp [hq]

private theorem main {O R τ : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Fintype τ] [DecidableEq τ]
    (W : WPres O (ℤ × ℤ) R) (h : W.HasOrigin)
    (hw : ∀ i, (W.wt i).1 = -1 ∨ (W.wt i).1 = 0 ∨ (W.wt i).1 = 1) (A : Subalgebra O R)
    (hA : ∀ f, f ∈ A ↔ f ∈ ⨆ n : ℤ, W.part (0, n)) (wt : τ → ℤ × ℤ)
    (φ : W.A →ₐ[O] MvPowerSeries τ (FractionRing O)) (H : IsChart W.gr ((W.origin h).comp W.A.val) wt φ)
    (b : τ) (hb : (wt b).1 = -1) (hτ : ∀ i, i ≠ b → (wt i).1 = 0 ∨ (wt i).1 = 1) :
    ∃ ψ : A →ₐ[O] MvPowerSeries {i // i ≠ b} (FractionRing O),
      IsChart (fun n : ℤ => (W.part (0, n)).comap A.val.toLinearMap) ((W.origin h).comp A.val)
        (fun i => (wt i.1).2 + (wt i.1).1 * (wt b).2) ψ := by
  classical
  have hAW : ∀ f, f ∈ A → f ∈ W.A := by
    intro f hf
    exact Submodule.iSup_induction _ (motive := fun z => z ∈ W.A) ((hA f).mp hf)
      (fun n z hz => W.part_le_A hz) (zero_mem _) (fun _ _ => add_mem)
  let incl : A →ₐ[O] W.A := Subalgebra.inclusion (fun f hf => hAW f hf)
  let φ' : A →ₐ[O] MvPowerSeries τ (FractionRing O) := φ.comp incl
  obtain ⟨ι, hιinj, hιs, hιw, hιr⟩ := iota wt b hb hτ
  have hgr : ∀ (f : A) (n : ℤ), (f : R) ∈ W.part (0, n) →
      φ' f ∈ wtPart (FractionRing O) wt (0, n) := fun f n hf => H.graded (0, n) (incl f) hf
  have hsupp : ∀ (f : A), ∀ m ∉ Set.range ι, MvPowerSeries.coeff m (φ' f) = 0 := by
    rintro ⟨f, hf⟩ m hm
    refine Submodule.iSup_induction' _
      (motive := fun z hz => MvPowerSeries.coeff m (φ' ⟨z, (hA z).mpr hz⟩) = 0) ?_ ?_ ?_ ((hA f).mp hf)
    · intro n z hz
      have hw : ∀ n', Finsupp.weight wt n' ≠ ((0 : ℤ), n) → MvPowerSeries.coeff n' (φ' ⟨z, (hA z).mpr (Submodule.mem_iSup_of_mem n hz)⟩) = 0 :=
        hgr ⟨z, _⟩ n hz
      by_contra hne
      apply hm
      apply hιr
      have := not_not.mp (mt (hw m) hne)
      rw [this]
    · show MvPowerSeries.coeff m (φ' 0) = 0
      simp
    · intro x y hx hy ihx ihy
      show MvPowerSeries.coeff m (φ' (⟨x, (hA x).mpr hx⟩ + ⟨y, (hA y).mpr hy⟩)) = 0
      rw [map_add, map_add, ihx, ihy, add_zero]
  obtain ⟨ψ, hψ⟩ := restrict φ' ι hιinj hsupp
  refine ⟨ψ, ?_⟩
  obtain ⟨g, hg⟩ := homog_gens H
  have hτ1 : ∀ i, i ≠ b → (wt i).1 ≠ 0 → (wt i).1 = 1 := fun i hi h0 => (hτ i hi).resolve_left h0
  have gA : ∀ i, (wt i).1 = 0 → ((g i : W.A) : R) ∈ A := fun i hi => mem_A W hA hi (hg i).1
  have gbA : ∀ i, (wt i).1 = 1 → ((g i : R) * (g b : R)) ∈ A := fun i hi =>
    mem_A W hA (j := wt i + wt b) (by simp [hi, hb]) (SetLike.mul_mem_graded (hg i).1 (hg b).1)
  let G : {i // i ≠ b} → A := fun i =>
    if hi : (wt i.1).1 = 0 then ⟨g i.1, gA i.1 hi⟩ else ⟨(g i.1 : R) * (g b : R), gbA i.1 (hτ1 i.1 i.2 hi)⟩
  have hinclG : ∀ i, incl (G i) = if (wt i.1).1 = 0 then g i.1 else g i.1 * g b := by
    intro i
    apply Subtype.ext
    simp only [G]
    split_ifs <;> rfl
  have hcr : ∀ j k, crLin ψ j (G k) =
      MvPowerSeries.coeff (ι (Finsupp.single j 1)) (φ (incl (G k))) := by
    intro j k
    rw [crLin_apply, hψ]
    rfl
  have hφ0 : ∀ i, MvPowerSeries.coeff 0 (φ (g i)) = 0 := fun i => by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.const, (hg i).2.1, map_zero]
  have hlin : ∀ i i', i' ≠ i → MvPowerSeries.coeff (Finsupp.single i' 1) (φ (g i)) = 0 := fun i i' h => by
    rw [← crLin_apply]
    exact (hg i).2.2.2 i' h
  have hdiag : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) (φ (g i)) ≠ 0 := fun i => by
    rw [← crLin_apply]
    exact (hg i).2.2.1
  refine chart_of_span ?_ ?_ G ?_ ?_
  · intro n f hf n' hn'
    rw [hψ]
    have hw : ∀ m, Finsupp.weight wt m ≠ ((0 : ℤ), n) → MvPowerSeries.coeff m (φ' f) = 0 := hgr f n hf
    apply hw
    rw [hιw]
    intro h'
    exact hn' (Prod.ext_iff.mp h').2
  · intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ, map_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact H.const (incl f)
  · intro v hv
    have h0 : ∀ j : {i // i ≠ b}, (wt j.1).1 = 0 → v j = 0 := by
      intro j hj
      have hj1 : ¬ (wt j.1).1 = 1 := by rw [hj]; norm_num
      have := hv j
      rw [Finset.sum_eq_single j] at this
      · rw [hcr, hιs, if_neg hj1, add_zero, hinclG, if_pos hj] at this
        exact (mul_eq_zero.mp this).resolve_right (hdiag j.1)
      · intro k _ hkj
        rw [hcr, hιs, if_neg hj1, add_zero, hinclG]
        split_ifs with hk
        · rw [hlin k.1 j.1 (fun h => hkj (Subtype.ext h).symm), mul_zero]
        · rw [map_mul, exists_ne_zero_smul_mem_of_mem_span' _ _ (hφ0 _) (hφ0 _), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h1 : ∀ j : {i // i ≠ b}, (wt j.1).1 = 1 → v j = 0 := by
      intro j hj
      have hj0 : ¬ (wt j.1).1 = 0 := by rw [hj]; norm_num
      have := hv j
      rw [Finset.sum_eq_single j] at this
      · rw [hcr, hιs, if_pos hj, hinclG, if_neg hj0, map_mul,
          coeff_two _ _ j.1 b j.1 (hφ0 _) (hφ0 _) (hlin j.1) (hlin b), if_pos rfl] at this
        exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero (hdiag _) (hdiag _))
      · intro k _ hkj
        rw [hcr, hιs, if_pos hj, hinclG]
        split_ifs with hk
        · rw [h0 k hk, zero_mul]
        · rw [map_mul, coeff_two _ _ k.1 b j.1 (hφ0 _) (hφ0 _) (hlin k.1) (hlin b),
            if_neg (fun h => hkj (Subtype.ext h).symm), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    funext j
    rcases hτ j.1 j.2 with h | h
    · exact h0 j h
    · exact h1 j h
  · intro f hf0
    let K : Ideal W.A := RingHom.ker ((W.origin h).comp W.A.val)
    have hK : ∀ (n : ℕ) (y : W.A), y ∈ K ^ n → (y : R) ∈ RingHom.ker (W.origin h) ^ n := by
      intro n y hy
      have hle : Ideal.map W.A.val (K ^ n) ≤ RingHom.ker (W.origin h) ^ n := by
        rw [Ideal.map_pow]
        apply Ideal.pow_right_mono
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        exact hz
      exact hle (Ideal.mem_map_of_mem _ hy)
    let Lsp : Submodule O A := Submodule.span O (Set.range G) ⊔
      (RingHom.ker ((W.origin h).comp A.val) ^ 2).restrictScalars O
    let L : Submodule O R := Lsp.map A.val.toLinearMap
    let N : Submodule O R :=
      { carrier := {y | ∃ c : O, c ≠ 0 ∧ c • y ∈ L}
        add_mem' := by
          rintro y₁ y₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
          refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
          have e : (c₁ * c₂) • (y₁ + y₂) = c₂ • c₁ • y₁ + c₁ • c₂ • y₂ := by
            rw [smul_add, smul_smul, smul_smul, mul_comm c₂ c₁]
          rw [e]
          exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
        zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
        smul_mem' := by
          rintro r y ⟨c, hc, h'⟩
          refine ⟨c, hc, ?_⟩
          rw [smul_comm]
          exact L.smul_mem _ h' }
    have hN : ∀ a ∈ A, ∀ b' ∈ A, W.origin h a = 0 → W.origin h b' = 0 → a * b' ∈ N := by
      intro a ha b' hb' ha0 hb0
      refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      refine Submodule.mem_map.mpr ⟨⟨a, ha⟩ * ⟨b', hb'⟩, Submodule.mem_sup_right ?_, rfl⟩
      show (⟨a, ha⟩ * ⟨b', hb'⟩ : A) ∈ RingHom.ker ((W.origin h).comp A.val) ^ 2
      rw [pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr ha0) (RingHom.mem_ker.mpr hb0)
    have hsat : ∀ c : O, c ≠ 0 → ∀ y, c • y ∈ N → y ∈ N := by
      rintro c hc y ⟨c', hc', h'⟩
      exact ⟨c' * c, mul_ne_zero hc' hc, by rw [mul_smul]; exact h'⟩
    let Γ : τ → R := fun k => if (wt k).1 = 0 then (g k : R) else (g k : R) * (g b : R)
    have hΓ : ∀ a : τ → O, a b = 0 → ∑ k, a k • Γ k = A.val (∑ i : {i // i ≠ b}, a i.1 • G i) := by
      intro a hab
      rw [Fintype.sum_eq_add_sum_subtype_ne _ b, hab, zero_smul, zero_add, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      congr 1
      simp only [Γ, G]
      split_ifs <;> rfl
    have hΓN : ∀ a : τ → O, a b = 0 → ∑ k, a k • Γ k ∈ N ∧ ∑ k, a k • Γ k ∈ A := by
      intro a hab
      rw [hΓ a hab]
      refine ⟨⟨1, one_ne_zero, ?_⟩, Subtype.prop _⟩
      rw [one_smul]
      refine Submodule.mem_map.mpr ⟨_, Submodule.mem_sup_left ?_, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hzs0 : ∀ s, ((W.origin h).comp W.A.val) (W.zA s) = 0 := by
      intro s
      show W.origin h (W.π (MvPowerSeries.X s)) = 0
      rw [WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have hgK : ∀ k, g k ∈ K := fun k => (hg k).2.1
    have hh1 : ∀ s, (W.wt s).1 = 0 → ∃ c : O, c ≠ 0 ∧ ∃ y ∈ N, y ∈ A ∧
        c • W.z s - y ∈ RingHom.ker (W.origin h) ^ 2 := by
      intro s hs
      obtain ⟨c, hc, a, ha, hm⟩ := _root_.expand H hg (j := W.wt s) (p := W.zA s) (W.z_mem s) (hzs0 s)
      have hab : a b = 0 := ha b (fun e => by
        have := congrArg Prod.fst e
        rw [hb, hs] at this
        norm_num at this)
      have hsum : ∑ k, a k • (g k : R) = ∑ k, a k • Γ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : a k = 0
        · rw [hk, zero_smul, zero_smul]
        · have hwk : wt k = W.wt s := by
            by_contra hne
            exact hk (ha k hne)
          have hk0 : (wt k).1 = 0 := by rw [hwk, hs]
          simp only [Γ, if_pos hk0]
      obtain ⟨hN', hA'⟩ := hΓN a hab
      refine ⟨c, hc, _, hN', hA', ?_⟩
      rw [← hsum]
      have e : W.A.val (c • W.zA s - ∑ k, a k • g k) = c • W.z s - ∑ k, a k • (g k : R) := by
        rw [map_sub, map_smul, map_sum]
        simp only [map_smul]
        rfl
      rw [← e]
      exact hK 2 _ hm
    have hh2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → ∃ c : O, c ≠ 0 ∧ ∃ y ∈ N, y ∈ A ∧
        c • (W.z s * W.z t) - y ∈ RingHom.ker (W.origin h) ^ 3 := by
      intro s t hs ht
      obtain ⟨c₁, hc₁, a₁, ha₁, hm₁⟩ :=
        _root_.expand H hg (j := W.wt s) (p := W.zA s) (W.z_mem s) (hzs0 s)
      obtain ⟨c₂, hc₂, a₂, ha₂, hm₂⟩ :=
        _root_.expand H hg (j := W.wt t) (p := W.zA t) (W.z_mem t) (hzs0 t)
      have hb1 : a₁ b = 0 := ha₁ b (fun e => by
        have := congrArg Prod.fst e
        rw [hb, hs] at this
        norm_num at this)
      have ha₂b : ∀ k, k ≠ b → a₂ k = 0 := fun k hk => ha₂ k (fun e => by
        have := congrArg Prod.fst e
        rw [ht] at this
        rcases hτ k hk with h' | h' <;> rw [h'] at this <;> norm_num at this)
      have hsum2 : ∑ k, a₂ k • g k = a₂ b • g b :=
        Fintype.sum_eq_single b (fun k hk => by rw [ha₂b k hk, zero_smul])
      rw [hsum2] at hm₂
      have huK : (∑ k, a₁ k • g k) ∈ K :=
        Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (hgK k)
      have hvK : a₂ b • g b ∈ K := Submodule.smul_of_tower_mem _ _ (hgK b)
      have hid : (c₁ • W.zA s) * (c₂ • W.zA t) - (∑ k, a₁ k • g k) * (a₂ b • g b) =
          (c₁ • W.zA s - ∑ k, a₁ k • g k) * (c₂ • W.zA t - a₂ b • g b) +
            (c₁ • W.zA s - ∑ k, a₁ k • g k) * (a₂ b • g b) +
              (∑ k, a₁ k • g k) * (c₂ • W.zA t - a₂ b • g b) := by ring
      have hm3 : (c₁ • W.zA s) * (c₂ • W.zA t) - (∑ k, a₁ k • g k) * (a₂ b • g b) ∈ K ^ 3 := by
        rw [hid]
        refine add_mem (add_mem ?_ ?_) ?_
        · refine Ideal.pow_le_pow_right (by norm_num : 3 ≤ 4) ?_
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hm₁ hm₂
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hm₁ hvK
        · rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
          exact Ideal.mul_mem_mul huK hm₂
      let a : τ → O := fun k => a₁ k * a₂ b
      have hab : a b = 0 := by simp [a, hb1]
      have hsum : W.A.val ((∑ k, a₁ k • g k) * (a₂ b • g b)) = ∑ k, a k • Γ k := by
        rw [map_mul, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : a₁ k = 0
        · simp [a, hk]
        · have hwk : wt k = W.wt s := by
            by_contra hne
            exact hk (ha₁ k hne)
          have hk0 : ¬ (wt k).1 = 0 := by rw [hwk, hs]; norm_num
          simp only [Γ, a, if_neg hk0, map_smul]
          rw [smul_mul_smul_comm]
          rfl
      obtain ⟨hN', hA'⟩ := hΓN a hab
      refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, _, hN', hA', ?_⟩
      rw [← hsum]
      have e : W.A.val ((c₁ • W.zA s) * (c₂ • W.zA t) - (∑ k, a₁ k • g k) * (a₂ b • g b)) =
          (c₁ * c₂) • (W.z s * W.z t) - W.A.val ((∑ k, a₁ k • g k) * (a₂ b • g b)) := by
        rw [map_sub, map_mul (W.A.val) (c₁ • W.zA s), map_smul, map_smul, smul_mul_smul_comm]
        rfl
      rw [← e]
      exact hK 3 _ hm3
    obtain ⟨c, hc, hcL⟩ := ker_le W h hw hA N hN hsat hh1 hh2 (f : R) f.2 hf0
    obtain ⟨w, hw', hwe⟩ := Submodule.mem_map.mp hcL
    have hwf : w = c • f := Subtype.ext hwe
    rw [hwf] at hw'
    obtain ⟨u, hu, p, hp, hup⟩ := Submodule.mem_sup.mp hw'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hu
    refine ⟨c, hc, a, ?_⟩
    rw [← hup, add_sub_cancel_left]
    exact hp

end PartC

private theorem count {τ : Type} [Fintype τ] [DecidableEq τ] (wt : τ → ℤ × ℤ) (r r' m : ℕ)
    (hn : ∀ j, Nat.card {i // wt i = j} = tDims r r' m j) :
    ∃ b : τ, (wt b).1 = -1 ∧ (∀ i, i ≠ b → (wt i).1 = 0 ∨ (wt i).1 = 1) ∧
      ∀ j, Nat.card {i : {i // i ≠ b} // (wt i.1).2 + (wt i.1).1 * (wt b).2 = j} = mDims r 0 r' 0 m j := by
  classical
  have hc : ∀ j, Fintype.card {i // wt i = j} = tDims r r' m j := fun j => by
    rw [← Nat.card_eq_fintype_card]
    exact hn j
  have hT : ∀ i, wt i = wAl ∨ wt i = wBe ∨ wt i = wTh ∨ wt i = wPs ∨ wt i = -wPs ∨ wt i = 0 := by
    intro i
    have h1 : 0 < Fintype.card {k // wt k = wt i} := Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
    rw [hc] at h1
    unfold tDims at h1
    split_ifs at h1 <;> first | tauto | omega
  have h1 : Fintype.card {i // wt i = wBe} = 1 := by
    rw [hc]
    simp [tDims]
  obtain ⟨⟨b, hb⟩, hbu⟩ := Fintype.card_eq_one_iff.mp h1
  have hne : ∀ i, i ≠ b → wt i ≠ wBe := fun i hi h => hi (congrArg Subtype.val (hbu ⟨i, h⟩))
  refine ⟨b, by rw [hb]; rfl, ?_, ?_⟩
  · intro i hi
    rcases hT i with h | h | h | h | h | h
    · right; simp [h, wAl]
    · exact absurd h (hne i hi)
    · right; simp [h, wTh]
    · left; simp [h, wPs]
    · left; simp [h, wPs]
    · left; simp [h]
  · intro j
    rw [Nat.card_eq_fintype_card, Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun i => i ≠ b) (fun i => (wt i).2 + (wt i).1 * (wt b).2 = j)), Fintype.card_subtype]
    rw [hb]
    have hterm : ∀ w : ℤ × ℤ, ((Finset.univ.filter fun i => i ≠ b ∧ (wt i).2 + (wt i).1 * wBe.2 = j).filter
        fun a => wt a = w).card = if w ≠ wBe ∧ w.2 + w.1 = j then tDims r r' m w else 0 := by
      intro w
      have hw1 : wBe.2 = 1 := rfl
      split_ifs with hw
      · rw [← hc, Fintype.card_subtype]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hw1, mul_one]
        constructor
        · rintro ⟨_, h⟩
          exact h
        · intro h
          refine ⟨⟨fun hib => hw.1 (h ▸ hib ▸ hb), h ▸ hw.2⟩, h⟩
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi hwi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hw1, mul_one] at hi
        apply hw
        subst hwi
        exact ⟨hne i hi.1, hi.2⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := wt)
      (t := ({wAl, wBe, wTh, wPs, -wPs, 0} : Finset (ℤ × ℤ))) (fun i _ => by simpa using hT i)]
    simp only [hterm]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have e1 : tDims r r' m wAl = 1 := by simp [tDims]
    have e2 : tDims r r' m wTh = 1 := by simp [tDims]
    have e3 : tDims r r' m wPs = r' := by simp [tDims, wAl, wBe, wTh, wPs]
    have e4 : tDims r r' m (-wPs) = r := by simp [tDims, wAl, wBe, wTh, wPs]
    have e5 : tDims r r' m 0 = m := by
      unfold tDims
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    rw [e1, e2, e3, e4, e5]
    have n1 : wAl ≠ wBe := by decide
    have n2 : wTh ≠ wBe := by decide
    have n3 : wPs ≠ wBe := by decide
    have n4 : -wPs ≠ wBe := by decide
    have n5 : (0 : ℤ × ℤ) ≠ wBe := by decide
    simp only [n1, n2, n3, n4, n5, ne_eq, not_false_eq_true, true_and, not_true_eq_false, false_and,
      if_false, zero_add]
    have s1 : wAl.2 + wAl.1 = 1 := rfl
    have s2 : wTh.2 + wTh.1 = 2 := rfl
    have s3 : wPs.2 + wPs.1 = 1 := rfl
    have s4 : (-wPs).2 + (-wPs).1 = -1 := rfl
    have s5 : (0 : ℤ × ℤ).2 + (0 : ℤ × ℤ).1 = 0 := rfl
    rw [s1, s2, s3, s4, s5]
    unfold mDims
    split_ifs <;> omega

theorem UpperTheory.V.GradeZeroInterpolatingElement.aSmooth :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, SmoothPt M.gr M.x0 (mDims M.r 0 M.r' 0 M.m) := by
  intro Ω _ _ _ l _ c D _ M
  obtain ⟨τ, hτ, wt, φ, H, hn⟩ := M.smooth
  classical
  obtain ⟨b, hb, hτb, hcount⟩ := count wt M.r M.r' M.m hn
  have hw : ∀ i, (M.W.wt i).1 = -1 ∨ (M.W.wt i).1 = 0 ∨ (M.W.wt i).1 = 1 := by
    intro i
    have := M.wt_mem i
    simp only [wts, oddRoots, wAl, wBe, wTh, wPs, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at this
    rcases this with ((h | h | h | h | h | h) | h | h | h) <;> rw [h] <;> simp
  obtain ⟨ψ, hψ⟩ := main M.W M.org hw M.A (fun f => Iff.rfl) wt φ H b hb hτb
  exact ⟨{i // i ≠ b}, inferInstance, _, ψ, hψ, hcount⟩
