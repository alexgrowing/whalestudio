import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DensePiDecomposition

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pi_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem pi_wcomp_mul {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X} (j : X)
    (a : MvPowerSeries σ O) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt c) :
    wcomp O wt j (a * h) = wcomp O wt (j - c) a * h := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 (wcomp O wt (j - c) a) * coeff p.2 h =
      if Finsupp.weight wt n = j then coeff p.1 a * coeff p.2 h else 0 := by
    intro p hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · have hn : Finsupp.weight wt n = Finsupp.weight wt p.1 + c := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add, h2]
      rw [coeff_wcomp, hn]
      by_cases h1 : Finsupp.weight wt p.1 = j - c
      · rw [if_pos h1, if_pos (by rw [h1]; abel)]
      · rw [if_neg h1, if_neg (fun h => h1 (by rw [← h]; abel)), zero_mul]
    · rw [hh _ h2]; simp
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

section

variable {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type} [CommRing R]
  [Algebra O R] [IsCO O R] (W : WPres O X R)

private theorem pi_max_le (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i} := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := pi_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : algebraMap O R (constantCoeff f) ∈ W.part 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  have h5 := h2 (Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i})
    fun s => Ideal.subset_span ⟨hz s, _, W.z_mem s⟩
  simpa using add_mem h5 (Ideal.subset_span ⟨h3, _, h4⟩)

private theorem pi_pow_le (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) :
    maximalIdeal R ^ N ≤ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i} := by
  induction N with
  | zero =>
    intro x _
    have : (1 : R) ∈ Ideal.span {y | y ∈ maximalIdeal R ^ 0 ∧ ∃ i, y ∈ W.part i} :=
      Ideal.subset_span ⟨by simp, 0, SetLike.GradedOne.one_mem⟩
    simpa using Ideal.mul_mem_left _ x this
  | succ N ih =>
    refine le_trans (le_of_eq (pow_succ _ _)) (le_trans (Ideal.mul_mono ih (pi_max_le W hz)) ?_)
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨a, ⟨ha, i, hi⟩, b, ⟨hb, k, hk⟩, rfl⟩
    refine Ideal.subset_span ⟨?_, i + k, SetLike.GradedMul.mul_mem hi hk⟩
    rw [pow_succ]
    exact Ideal.mul_mem_mul ha hb

private theorem pi_dense (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (x : R) :
    ∃ a ∈ W.A, x - a ∈ maximalIdeal R ^ N :=
  by apply _root_.UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense <;> assumption

private theorem pi_homog (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (f : MvPowerSeries W.σ O)
    (hf : W.π f ∈ maximalIdeal R ^ N) (j : X) : W.π (wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
  have key : ∀ y ∈ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i},
      ∃ g, W.π g = y ∧ ∀ a j, W.π (wcomp O W.wt j (a * g)) ∈ maximalIdeal R ^ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨ht, i, g, hg, rfl⟩ := ht
      refine ⟨g, rfl, fun a j => ?_⟩
      rw [pi_wcomp_mul W.wt j a hg, map_mul]
      exact Ideal.mul_mem_left _ _ ht
    | zero => exact ⟨0, map_zero _, fun a j => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨g', rfl, hg'⟩ := hz
      refine ⟨g + g', map_add _ _ _, fun a j => ?_⟩
      rw [mul_add, map_add, map_add]
      exact add_mem (hg a j) (hg' a j)
    | smul r y _ hy =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨q, rfl⟩ := W.surj r
      refine ⟨q * g, map_mul _ _ _, fun a j => ?_⟩
      rw [← mul_assoc]
      exact hg _ j
  obtain ⟨g, hg, hg'⟩ := key _ (pi_pow_le W hz N hf)
  have h1 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hg, sub_self]
  have h2 := W.homog _ h1 j
  rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at h2
  rw [h2]
  simpa using hg' 1 j

end

theorem UpperTheory.V.Alg.pres_indep :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ W' : WPres O X R, (∀ s, W'.z s ∈ maximalIdeal R) → (∀ s, W'.z s ∈ W.part (W'.wt s)) → ∀ j, W'.part j = W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz W' hz' hw j
  have hle : ∀ i, ∀ x ∈ W'.part i, x ∈ W.part i :=
    UpperTheory.V.Alg.map_part O X R W' hz' R W hz (AlgHom.id O R) hw
  refine le_antisymm (hle j) fun x hx => ?_
  refine UpperTheory.V.Alg.part_closed O X R W' hz' j x fun N => ?_
  obtain ⟨a, ha, hxa⟩ := pi_dense W' hz' N x
  have ha' : a ∈ ⨆ i, W'.part i := ha
  have hself : ∀ g ∈ wtPart O W.wt j, wcomp O W.wt j g = g := by
    intro g hg
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hg n h).symm
  have key : ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j := by
    refine Submodule.iSup_induction W'.part
      (motive := fun a => ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j) ha' ?_ ?_ ?_
    · intro i y hy
      obtain ⟨f, hf, hfy⟩ := hle i y hy
      have hfy' : W.π f = y := hfy
      refine ⟨f, hfy', ?_⟩
      by_cases hij : i = j
      · subst hij
        rw [hself f hf, hfy']
        exact hy
      · have : wcomp O W.wt j f = 0 := by
          ext n
          rw [coeff_wcomp]
          split_ifs with h
          · rw [hf n (fun h' => hij (h'.symm.trans h))]; simp
          · simp
        rw [this, map_zero]
        exact zero_mem _
    · exact ⟨0, map_zero _, by simp⟩
    · rintro a b ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
      refine ⟨f + g, by rw [map_add, hf, hg], ?_⟩
      rw [map_add, map_add]
      exact add_mem hf' hg'
  obtain ⟨f, hf, hf'⟩ := key
  obtain ⟨g, hg, hgx⟩ := hx
  have hgx' : W.π g = x := hgx
  refine ⟨_, hf', ?_⟩
  have := pi_homog W hz N (g - f) (by rwa [map_sub, hgx', hf]) j
  rwa [map_sub, hself g hg, map_sub, hgx'] at this
