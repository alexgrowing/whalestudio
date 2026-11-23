import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wt_add' (i j k : Fin 4) : wt i j + wt j k = wt i k := by
  simp [wt]

private theorem laurent_mul_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X Y : M4 S) (X0 Y0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j))
    (hY : ∀ i j, e (Y i j) = HahnSeries.single (τ (wt i j)) (Y0 i j)) (i j : Fin 4) :
    e ((X * Y) i j) = HahnSeries.single (τ (wt i j)) ((X0 * Y0) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [map_add e, map_mul, hX, hY, HahnSeries.single_mul_single, ← map_add τ, wt_add',
    HahnSeries.single_add]

private theorem laurent_adj_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X : M4 S) (X0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j)) (i j : Fin 4) :
    e ((adj X) i j) = HahnSeries.single (τ (wt i j)) ((adj X0) i j) := by
  have hrev : ∀ i j : Fin 4, wt j.rev i.rev = wt i j := by decide
  simp only [adj, Matrix.of_apply, zsmul_eq_mul, map_mul, map_intCast, hX, hrev]
  rw [← map_intCast (HahnSeries.C : R →+* LaurentSeries R), HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add]

private theorem laurent_smul_one_apply_eq_single_of_eq_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (ν : S) (ν0 : R) (hν : e ν = HahnSeries.single 0 ν0) (i j : Fin 4) :
    e ((ν • (1 : M4 S)) i j) = HahnSeries.single (τ (wt i j)) ((ν0 • (1 : M4 R)) i j) := by
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, hν, hw0]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h]

theorem UpperTheory.V.Ws.sxScaleRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R} {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R}, IsNilpotent (maximalIdeal R) → Laur Λ c e → (∀ i j, -(c : ℤ) ≤ τ (wt i j)) → Φ.Near a τ D → ∃ D' : RD Φ S, Φ.Near a 0 D' ∧ (∀ g i j, e (D'.r g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j)) ∧ ∀ v i s, e (D'.ψ v i s) = HahnSeries.single 0 (D.ψ v i s) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ S _ _ _ c e τ D hnil hL hc hN
  classical
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  have hresm : ∀ {T : Type} [CommRing T] [Algebra Λ T] [IsCO Λ T] (y : T), y ∈ maximalIdeal T →
      res Λ T y = 0 := by
    intro T _ _ _ y hy
    simp [res, (IsLocalRing.residue_eq_zero_iff y).mpr hy]
  have hex0 : ∀ x : R, ∃ y : S, e y = HahnSeries.single 0 x ∧ res Λ S y = res Λ R x := by
    intro x
    obtain ⟨l, hl⟩ := IsCO.res_surj (O := Λ) x
    obtain ⟨y, hy, hye⟩ := hL.mem 0 _ (Or.inr ⟨by omega, hl⟩)
    refine ⟨y + algebraMap Λ S l, ?_, ?_⟩
    · rw [map_add, hye, hL.alg, ← HahnSeries.single_add, sub_add_cancel]
    · rw [map_add, hresm y hy, AlgHom.commutes, zero_add]
      conv_rhs => rw [← sub_add_cancel x (algebraMap Λ R l)]
      rw [map_add, hresm _ hl, AlgHom.commutes, zero_add]
  have hent : ∀ g i j, ∃ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) := by
    intro g i j
    rcases lt_trichotomy (τ (wt i j)) 0 with h | h | h
    · have hij : i ≠ j := by
        rintro rfl
        rw [hw0, map_zero] at h
        exact lt_irrefl _ h
      obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h.le⟩)
      exact ⟨y, hy⟩
    · rw [h]
      obtain ⟨y, hy, -⟩ := hex0 (D.r g i j)
      exact ⟨y, hy⟩
    · obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inl h)
      exact ⟨y, hy⟩
  have hmem : ∀ g i j, i ≠ j → ∀ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) →
      y ∈ maximalIdeal S := by
    intro g i j hij y hy
    rcases le_or_gt (τ (wt i j)) 0 with h | h
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h⟩)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inl h)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
  let pre : LaurentSeries R → S := fun z => if h : ∃ y, e y = z then h.choose else 0
  have hpre : ∀ z, (∃ y, e y = z) → e (pre z) = z := by
    intro z h
    simp only [pre, dif_pos h]
    exact h.choose_spec
  have hpre0 : ∀ x : R, e (pre (HahnSeries.single 0 x)) = HahnSeries.single 0 x := by
    intro x
    obtain ⟨y, hy, -⟩ := hex0 x
    exact hpre _ ⟨y, hy⟩
  have hres0 : ∀ x : R, res Λ S (pre (HahnSeries.single 0 x)) = res Λ R x := by
    intro x
    obtain ⟨y, hy, hr⟩ := hex0 x
    rw [hL.inj ((hpre0 x).trans hy.symm)]
    exact hr
  let rr : Γ → M4 S := fun g => Matrix.of fun i j => pre (HahnSeries.single (τ (wt i j)) (D.r g i j))
  have hrr : ∀ g i j, e (rr g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) :=
    fun g i j => hpre _ (hent g i j)
  have hext : ∀ X Y : M4 S, (∀ i j, e (X i j) = e (Y i j)) → X = Y :=
    fun X Y h => Matrix.ext fun i j => hL.inj (h i j)
  have h1 : ∀ i j, e ((1 : M4 S) i j) = HahnSeries.single (τ (wt i j)) ((1 : M4 R) i j) := by
    intro i j
    have := laurent_smul_one_apply_eq_single_of_eq_single e τ 1 1 (by rw [map_one, HahnSeries.single_zero_one]) i j
    simpa only [one_smul] using this
  let r' : Γ →* M4 S :=
    { toFun := rr
      map_one' := hext _ _ fun i j => by rw [hrr, D.r.map_one, h1]
      map_mul' := fun g h => hext _ _ fun i j => by
        rw [hrr, D.r.map_mul, laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (hrr g) (hrr h)] }
  have hr' : ∀ g i j, e (r' g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) := hrr
  let ψ' : (v : Φ.ι) → Fin 4 → ↥(Φ.Gv v) →* S := fun v i =>
    { toFun := fun s => pre (HahnSeries.single 0 (D.ψ v i s))
      map_one' := hL.inj (by rw [hpre0, (D.ψ v i).map_one, HahnSeries.single_zero_one, map_one])
      map_mul' := fun s t => hL.inj (by
        rw [hpre0, (D.ψ v i).map_mul, map_mul e, hpre0, hpre0, HahnSeries.single_mul_single, zero_add]) }
  obtain ⟨K, hK⟩ := hnil
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal R ^ K)) := by
    intro x y h
    rwa [Ideal.Quotient.eq, hK, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at h
  refine ⟨⟨r', ψ'⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hr', fun v i s => hpre0 _⟩
  · intro g
    have hg : adj (D.r g) * D.r g = _ := hN.rep.mult g
    show adj (r' g) * r' g = _
    simp only [RingHom.comp_apply] at hg ⊢
    refine hext _ _ fun i j => ?_
    rw [laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (laurent_adj_apply_eq_single_of_entries_single e τ _ _ (hr' g)) (hr' g), hg,
      laurent_smul_one_apply_eq_single_of_eq_single e τ _ _ (hL.alg _)]
  · intro g hg
    refine hext _ _ fun i j => ?_
    rw [hr', hN.rep.kill g hg, h1]
  · intro i j hij
    apply hL.inj
    rw [hr', hN.rep.nrm hij, HahnSeries.single_eq_zero, map_zero]
  · intro i j N
    have h2 : IsLocallyConstant fun g => D.r g i j :=
      IsLocallyConstant.desc _ _ (hN.cont i j K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single (τ (wt i j)) x)))
  · intro v i N
    have h2 : IsLocallyConstant fun s => D.ψ v i s :=
      IsLocallyConstant.desc _ _ (hN.contψ v i K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single 0 x)))
  · intro g i
    rw [← hN.diag g i]
    show res Λ S (pre (HahnSeries.single (τ (wt i i)) (D.r g i i))) = _
    rw [hw0, map_zero]
    exact hres0 _
  · intro g i j hij _
    exact hmem g i j hij _ (hr' g i j)
  · intro v i s
    rw [← hN.redψ v i s]
    exact hres0 _
