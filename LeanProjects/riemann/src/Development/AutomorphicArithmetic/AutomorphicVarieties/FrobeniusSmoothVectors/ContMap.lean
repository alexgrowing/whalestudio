import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem mon_part {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R)
    (h : ∀ g i j, ρ.r g i j ∈ W.part (w n i - w n j)) {j : ℤ} {x : R} (hx : x ∈ ρ.mon j) : x ∈ W.part j := by
  obtain ⟨L, hL, rfl⟩ := hx
  rw [← hL]
  exact SetLike.list_prod_map_mem_graded L _ _ fun s _ => h s.1 s.2.1 s.2.2

private theorem mono_lemma {l : ℕ} [Fact l.Prime] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] (ρ : NRep F n R) {a b : ℤ} {x y : R} (hx : x ∈ ρ.mon a) (hy : y ∈ ρ.mon b) :
    x * y ∈ ρ.mon (a + b) := by
  obtain ⟨L1, h1, rfl⟩ := hx
  obtain ⟨L2, h2, rfl⟩ := hy
  exact ⟨L1 ++ L2, by simp [h1, h2], by simp⟩

private theorem mono_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (s : W.σ) (e : ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (e • W.wt s), W.z s ^ e = b * x := by
  induction e with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | succ e ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    rcases h s with ⟨g, i, j, hz, hw⟩ | ⟨hw, hz⟩
    · have hs : ρ.r g i j ∈ ρ.mon (W.wt s) := ⟨[(g, i, j)], by simp [hw], by simp⟩
      refine ⟨b, hb, x * ρ.r g i j, ?_, ?_⟩
      · rw [succ_nsmul]
        exact mono_lemma ρ hx hs
      · rw [pow_succ, hbx, hz]
        ring
    · refine ⟨b * W.z s, D.mul_mem hb hz, x, ?_, ?_⟩
      · simpa [hw] using hx
      · rw [pow_succ, hbx]
        ring

private theorem mono {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (m : W.σ →₀ ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (Finsupp.weight W.wt m), W.π (MvPowerSeries.monomial m 1) = b * x := by
  induction m using Finsupp.induction with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | single_add a e f _ _ ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    obtain ⟨b', hb', x', hx', hbx'⟩ := mono_lemma_2 ρ W D h a e
    refine ⟨b' * b, D.mul_mem hb' hb, x' * x, ?_, ?_⟩
    · have hw : Finsupp.weight W.wt (Finsupp.single a e) = e • W.wt a := by
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      rw [map_add, hw]
      exact mono_lemma ρ hx' hx
    · have hm : MvPowerSeries.monomial (Finsupp.single a e + f) (1 : O) =
          MvPowerSeries.X a ^ e * MvPowerSeries.monomial f 1 := by
        rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
      simp only [WPres.z] at hbx'
      rw [hm, map_mul, map_pow, hbx, hbx']
      ring

private theorem dense {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (D : Subalgebra O R)
    (hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D) {y : R} (hy : y ∈ W.part 0) :
    y ∈ adicClosure D := by
  haveI := W.fin
  classical
  simp only [WPres.part, Submodule.mem_map] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  have hf' : ∀ m, Finsupp.weight W.wt m ≠ 0 → MvPowerSeries.coeff m f = 0 := hf
  have key : ∀ m, W.π (MvPowerSeries.monomial m (MvPowerSeries.coeff m f)) ∈ D := by
    intro m
    by_cases hm : Finsupp.weight W.wt m = 0
    · have e : MvPowerSeries.monomial m (MvPowerSeries.coeff m f) =
          MvPowerSeries.coeff m f • MvPowerSeries.monomial m (1 : O) := by
        rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact D.smul_mem (hD m hm) _
    · rw [hf' m hm, map_zero, map_zero]
      exact D.zero_mem
  simp only [AlgHom.toLinearMap_apply]
  show ∀ N : ℕ, ∃ d ∈ D, W.π f - d ∈ maximalIdeal R ^ N
  intro N
  let c : W.σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  let low := ∑ m ∈ Finset.Iic c, MvPowerSeries.monomial m (MvPowerSeries.coeff m f)
  let S : Set (W.σ →₀ ℕ) := {m | Finsupp.weight W.wt m = 0 ∧ ∃ s, N ≤ m s}
  have hg : ∀ m ∉ S, MvPowerSeries.coeff m (f - low) = 0 := by
    intro m hm
    simp only [S, Set.mem_setOf_eq, not_and, not_exists, not_le] at hm
    have hl : MvPowerSeries.coeff m low = if m ∈ Finset.Iic c then MvPowerSeries.coeff m f else 0 := by
      simp [low, map_sum, MvPowerSeries.coeff_monomial]
    rw [map_sub, hl]
    by_cases hw : Finsupp.weight W.wt m = 0
    · have hmc : m ∈ Finset.Iic c := by
        rw [Finset.mem_Iic]
        intro s
        exact (hm hw s).le.trans_eq (by simp [c])
      simp [hmc]
    · simp [hf' m hw]
  obtain ⟨μ, hμ, hspan⟩ := part_span O R ℤ W S 0 (fun m hm => hm.1)
  obtain ⟨b, hb, hfb⟩ := hspan (f - low) hg
  refine ⟨W.π low, ?_, ?_⟩
  · rw [map_sum]
    exact Subalgebra.sum_mem _ fun m _ => key m
  · rw [← map_sub, hfb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨s, hs⟩ := (hμ (Finset.mem_coe.mpr hm)).2
    have e : MvPowerSeries.monomial m (1 : O) =
        MvPowerSeries.X s ^ N * MvPowerSeries.monomial (m - Finsupp.single s N) 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hs)]
    rw [map_mul, e, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hz s) N))

private theorem cont_map {O Γ R R' : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace Γ] [CommRing R] [Algebra O R]
    [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (c : R') {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => c * f (a g) := by
  have hm : Ideal.map f.toRingHom (maximalIdeal R) ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  intro N
  have hN : maximalIdeal R ^ N ≤ Ideal.comap f.toRingHom (maximalIdeal R' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (c * f (a g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal R' ^ N) c *
        Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hN q) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (a g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  rw [e]
  exact (ha N).comp _

private theorem twist_lemma {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C)
    (c : Fin n → Fin n → C) (hc : ∀ i, c i i = 1) (ρ' : NRep F n C)
    (hr : ∀ g i j, ρ'.r g i j = c i j * f (S.ρ.r g i j)) (hψ : ∀ v i g, (ρ'.ψ v i g : C) = f (S.ρ.ψ v i g)) :
    IsLift O ρ' := by
  obtain ⟨⟨hc1, hc2⟩, ⟨hb1, hb2⟩, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · simpa only [hr] using cont_map f (c i j) (hc1 i j)
  · simpa only [hψ, one_mul] using cont_map f 1 (hc2 v i)
  · show (res O C) (ρ'.r g i i) = _
    rw [hr, hc, one_mul, res_map]
    exact hb1 g i
  · show (res O C) ((ρ'.ψ v i g : Cˣ) : C) = _
    rw [hψ, res_map]
    exact hb2 v i g
  · show (res O C) (ρ'.r g i j) = 0
    rw [hr, map_mul, res_map]
    have h0 : (res O S.R) (S.ρ.r g i j) = 0 := hd g i j hij
    rw [h0, mul_zero]

private theorem twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C) (u : Cˣ) :
    ∃ f' : S.R →ₐ[O] C, (∀ g i j, f' (S.ρ.r g i j) = ((u ^ (w n i - w n j) : Cˣ) : C) * f (S.ρ.r g i j)) ∧
      ∀ v i g, f' (S.ρ.ψ v i g) = f (S.ρ.ψ v i g) := by
  obtain ⟨ρ', hr, hψ⟩ := alg_twist u (S.ρ.map (f : S.R →+* C))
  have hl : IsLift O ρ' := twist_lemma S C f (fun i j => ((u ^ (w n i - w n j) : Cˣ) : C)) (by simp) ρ'
    (fun g i j => by rw [hr]; rfl) (fun v i g => by rw [hψ]; rfl)
  obtain ⟨f', hf', -⟩ := S.univ C ρ' hl
  refine ⟨f', fun g i j => ?_, fun v i g => ?_⟩
  · calc f' (S.ρ.r g i j) = (S.ρ.map (f' : S.R →+* C)).r g i j := rfl
      _ = ρ'.r g i j := by rw [hf']
      _ = _ := by rw [hr]; rfl
  · calc f' (S.ρ.ψ v i g : S.R) = (((S.ρ.map (f' : S.R →+* C)).ψ v i g : Cˣ) : C) := rfl
      _ = (ρ'.ψ v i g : C) := by rw [hf']
      _ = _ := by rw [hψ]; rfl

private theorem uniq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : S.R →ₐ[O] C)
    (h1 : ∀ g i j, f (S.ρ.r g i j) = f' (S.ρ.r g i j)) (h2 : ∀ v i g, f (S.ρ.ψ v i g) = f' (S.ρ.ψ v i g)) :
    f = f' := by
  have hl : IsLift O (S.ρ.map (f : S.R →+* C)) := twist_lemma S C f (fun _ _ => 1) (fun _ => rfl) _
    (fun g i j => by rw [one_mul]; rfl) (fun v i g => rfl)
  refine (S.univ C _ hl).unique rfl (NRep.ext ?_ ?_)
  · exact MonoidHom.ext fun g => Matrix.ext fun i j => (h1 g i j).symm
  · funext v i
    exact MonoidHom.ext fun g => Units.ext (h2 v i g).symm

private theorem coord {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) :
    ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧
      (∀ v i g, (S.ρ.ψ v i g : S.R) ∈ W.part 0) ∧
      ∀ s, (∃ g i j, W.z s = S.ρ.r g i j ∧ W.wt s = w n i - w n j) ∨
        (W.wt s = 0 ∧ W.z s ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})) := by
  classical
  let a : S.R → O := fun x => Classical.choose (IsCO.res_surj (O := O) x)
  have ha : ∀ x, x - algebraMap O S.R (a x) ∈ maximalIdeal S.R := fun x =>
    Classical.choose_spec (IsCO.res_surj (O := O) x)
  let e : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → S.R := Sum.elim
    (fun p => if p.2.1 = p.2.2 then S.ρ.r p.1 p.2.1 p.2.2 - algebraMap O S.R (a (S.ρ.r p.1 p.2.1 p.2.2))
      else S.ρ.r p.1 p.2.1 p.2.2)
    (fun q => (S.ρ.ψ q.1 q.2.1 q.2.2 : S.R) - algebraMap O S.R (a (S.ρ.ψ q.1 q.2.1 q.2.2)))
  let wt : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → ℤ := Sum.elim
    (fun p => w n p.2.1 - w n p.2.2) (fun _ => 0)
  have eon : ∀ g i, e (Sum.inl (g, i, i)) = S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) :=
    fun g i => if_pos rfl
  have eoff : ∀ g i j, i ≠ j → e (Sum.inl (g, i, j)) = S.ρ.r g i j := fun g i j h => if_neg h
  have eψ : ∀ v i g, e (Sum.inr ⟨v, i, g⟩) =
      (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) := fun v i g => rfl
  have hoff : ∀ g i j, i ≠ j → S.ρ.r g i j ∈ maximalIdeal S.R := fun g i j h =>
    (res_eq_zero_iff O S.R _).mp (by exact S.lift.2.2 g i j h)
  have he : ∀ s, e s ∈ maximalIdeal S.R := by
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases h : i = j
      · subst h
        rw [eon]
        exact ha _
      · rw [eoff g i j h]
        exact hoff g i j h
    · rw [eψ]
      exact ha _
  have huniq : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : S.R →ₐ[O] R'),
      (∀ s, f (e s) = f' (e s)) → f = f' := by
    intro R' _ _ _ f f' h
    apply uniq S R' f f'
    · intro g i j
      by_cases hij : i = j
      · subst hij
        have h1 := h (Sum.inl (g, i, i))
        rw [eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
        exact sub_left_injective h1
      · have h1 := h (Sum.inl (g, i, j))
        rw [eoff g i j hij] at h1
        exact h1
    · intro v i g
      have h1 := h (Sum.inr ⟨v, i, g⟩)
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
      exact sub_left_injective h1
  have htw : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : S.R →ₐ[O] R')
      (t : Multiplicative ℤ →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∃ f' : S.R →ₐ[O] R', ∀ s, f' (e s) = (t (Multiplicative.ofAdd (wt s)) : R') * f (e s) := by
    intro R' _ _ _ f t _
    obtain ⟨f', h1, h2⟩ := twist S R' f (t (Multiplicative.ofAdd 1))
    have ht : ∀ k : ℤ, t (Multiplicative.ofAdd k) = t (Multiplicative.ofAdd 1) ^ k := by
      intro k
      rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases hij : i = j
      · subst hij
        show f' (e (Sum.inl (g, i, i))) = (t (Multiplicative.ofAdd (w n i - w n i)) : R') * _
        rw [sub_self, eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · show f' (e (Sum.inl (g, i, j))) = (t (Multiplicative.ofAdd (w n i - w n j)) : R') * _
        rw [eoff g i j hij, h1, ht (w n i - w n j)]
    · show f' (e (Sum.inr ⟨v, i, g⟩)) = (t (Multiplicative.ofAdd 0) : R') * _
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h2]
      simp
  obtain ⟨W, u, hWu, hpart⟩ := coord_grading O ℤ S.R _ e wt he huniq htw
  have h1mem : ∀ c : O, algebraMap O S.R c ∈ W.part 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c SetLike.GradedOne.one_mem
  refine ⟨W, fun s => by rw [(hWu s).1]; exact he _, ?_, ?_, ?_⟩
  · intro g i j
    by_cases hij : i = j
    · subst hij
      have hp : S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) ∈ W.part 0 := by
        have := hpart (Sum.inl (g, i, i))
        rw [eon] at this
        simpa [wt] using this
      rw [sub_self, ← sub_add_cancel (S.ρ.r g i i) (algebraMap O S.R (a (S.ρ.r g i i)))]
      exact add_mem hp (h1mem _)
    · have hp := hpart (Sum.inl (g, i, j))
      rw [eoff g i j hij] at hp
      exact hp
  · intro v i g
    have hp : (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) ∈ W.part 0 :=
      hpart (Sum.inr ⟨v, i, g⟩)
    rw [← sub_add_cancel (S.ρ.ψ v i g : S.R) (algebraMap O S.R (a (S.ρ.ψ v i g)))]
    exact add_mem hp (h1mem _)
  · intro s
    obtain ⟨hz, hw⟩ := hWu s
    rcases hs : u s with ⟨g, i, j⟩ | ⟨v, i, g⟩
    · rw [hs] at hz hw
      by_cases hij : i = j
      · subst hij
        right
        refine ⟨by rw [hw]; exact sub_self _, ?_⟩
        rw [hz, eon]
        exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨[(g, i, i)], by simp, by simp⟩))
          (Subalgebra.algebraMap_mem _ _)
      · left
        exact ⟨g, i, j, by rw [hz, eoff g i j hij], hw⟩
    · rw [hs] at hz hw
      right
      refine ⟨hw, ?_⟩
      rw [hz, eψ]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩))
        (Subalgebra.algebraMap_mem _ _)

private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih]
    rfl

theorem UpperTheory.V.Fr.wpres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧ (∀ y, y ∈ S.B ↔ y ∈ W.part 0) ∧ S.A = W.A ∧ ∀ j (a : S.A), a ∈ S.gr j ↔ (a : S.R) ∈ W.part j := by
  intro l _ O _ _ _ _ F C₀ n _ _ S
  obtain ⟨W, hz, hr, hψ, hgen⟩ := coord S
  let D : Subalgebra O S.R := Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})
  have hmon : ∀ m, ∃ b ∈ D, ∃ x ∈ S.ρ.mon (Finsupp.weight W.wt m),
      W.π (MvPowerSeries.monomial m 1) = b * x := mono S.ρ W D hgen
  have hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D := by
    intro m hm
    obtain ⟨b, hb, x, hx, e⟩ := hmon m
    rw [e]
    rw [hm] at hx
    exact D.mul_mem hb (Algebra.subset_adjoin (Or.inl hx))
  have P0 : ∀ y, y ∈ W.part 0 → y ∈ S.B := fun y hy => dense W hz D hD hy
  let P : Subalgebra O S.R := (W.part 0).toSubalgebra SetLike.GradedOne.one_mem (fun x y hx hy => by
    have := SetLike.GradedMul.mul_mem hx hy
    rwa [add_zero] at this)
  have BP : ∀ y, y ∈ S.B → y ∈ W.part 0 := by
    intro y hy
    have hDP : D ≤ P := Algebra.adjoin_le (by
      rintro x (hx | ⟨v, i, g, rfl⟩)
      · exact mon_part S.ρ W hr hx
      · exact hψ v i g)
    have hy' : ∀ N : ℕ, ∃ d ∈ D, y - d ∈ maximalIdeal S.R ^ N := hy
    refine part_closed O ℤ S.R W hz 0 y fun N => ?_
    obtain ⟨d, hd, hyd⟩ := hy' N
    exact ⟨d, hDP hd, hyd⟩
  have dec : ∀ j y, y ∈ W.part j → ∃ μ : Finset (W.σ →₀ ℕ), ∃ c x : (W.σ →₀ ℕ) → S.R,
      (∀ m, c m ∈ S.B) ∧ (∀ m ∈ μ, x m ∈ S.ρ.mon j) ∧ y = ∑ m ∈ μ, c m * x m := by
    intro j y hy
    simp only [WPres.part, Submodule.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    obtain ⟨μ, hμ, hspan⟩ := part_span O S.R ℤ W {m | Finsupp.weight W.wt m = j} j (fun m hm => hm)
    obtain ⟨b, hb, hfb⟩ := hspan f (fun m hm => hf m hm)
    choose B hB X hX hBX using hmon
    refine ⟨μ, fun m => W.π (b m) * B m, X,
      fun m => S.B.mul_mem (P0 _ (Submodule.mem_map_of_mem (hb m))) (le_adicClosure D (hB m)),
      fun m hm => ?_, ?_⟩
    · have := hX m
      have hw : Finsupp.weight W.wt m = j := hμ (Finset.mem_coe.mpr hm)
      rwa [hw] at this
    · simp only [AlgHom.toLinearMap_apply]
      rw [hfb, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, hBX, mul_assoc]
  refine ⟨W, hz, hr, fun y => ⟨BP y, P0 y⟩, ?_, ?_⟩
  · apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro x (hx | ⟨g, i, j, rfl⟩)
      · exact W.part_le_A (BP x hx)
      · exact W.part_le_A (hr g i j)
    · intro x hx
      have hx' : x ∈ ⨆ j, W.part j := hx
      have hle : (⨆ j, W.part j) ≤ Subalgebra.toSubmodule S.A := by
        refine iSup_le fun j y hy => ?_
        rw [Subalgebra.mem_toSubmodule]
        obtain ⟨μ, c, X, hc, hX, rfl⟩ := dec j y hy
        refine Subalgebra.sum_mem _ fun m hm => S.A.mul_mem (Algebra.subset_adjoin (Or.inl (hc m))) ?_
        obtain ⟨L, -, hXL⟩ := hX m hm
        rw [hXL, ← val_prod S L]
        exact SetLike.coe_mem _
      exact hle hx'
  · intro j a
    constructor
    · intro ha
      refine Submodule.span_induction (p := fun (a : S.A) _ => (a : S.R) ∈ W.part j) ?_ ?_ ?_ ?_
        (show a ∈ Submodule.span S.B (S.u.mon j) from ha)
      · rintro x ⟨L, hL, rfl⟩
        rw [val_prod]
        exact mon_part S.ρ W hr ⟨L, hL, rfl⟩
      · simp
      · intro x y _ _ hx hy
        simpa using add_mem hx hy
      · intro b x _ hx
        have := SetLike.GradedMul.mul_mem (BP b b.2) hx
        rw [zero_add] at this
        have hbx : ((b • x : S.A) : S.R) = (b : S.R) * (x : S.R) := by
          first | rfl | simp [Algebra.smul_def] | simp [Subalgebra.smul_def]
        rw [hbx]
        exact this
    · intro ha
      obtain ⟨μ, c, X, hc, hX, e⟩ := dec j _ ha
      have hXu : ∀ m ∈ μ, ∃ a' ∈ S.u.mon j, (a' : S.R) = X m := by
        intro m hm
        obtain ⟨L, hL, e'⟩ := hX m hm
        exact ⟨_, ⟨L, hL, rfl⟩, by rw [val_prod, e']⟩
      choose! A' hA' hA'e using hXu
      have hsum : a = ∑ m ∈ μ, (⟨c m, hc m⟩ : S.B) • A' m := by
        apply Subtype.ext
        rw [e]
        simp only [AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [← hA'e m hm]
        rfl
      rw [hsum]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span (hA' m hm))
