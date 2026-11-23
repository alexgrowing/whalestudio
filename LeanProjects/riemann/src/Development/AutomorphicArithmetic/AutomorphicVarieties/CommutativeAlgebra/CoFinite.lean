import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, φ, hφ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have himg : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) = Submodule.map φ (I ^ n • ⊤) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hφ]
  refine ⟨fun {f} hf => ?_⟩
  have hmem : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n
    have := SModEq.sub_mem.1 (hf (Nat.le_succ n))
    rw [← neg_sub]
    exact neg_mem this
  have hd : ∀ n, ∃ d : Fin r → R, d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)) ∧ φ d = f (n + 1) - f n := by
    intro n
    have := hmem n
    rw [himg n, Submodule.mem_map] at this
    exact this
  choose d hdmem hdφ using hd
  obtain ⟨y0, hy0⟩ := hφ (f 0)
  set g : ℕ → (Fin r → R) := fun n => y0 + ∑ k ∈ Finset.range n, d k with hg
  have hgφ : ∀ n, φ (g n) = f n := by
    intro n
    induction n with
    | zero => simp [hg, hy0]
    | succ n ih =>
      have : g (n + 1) = g n + d n := by
        simp only [hg, Finset.sum_range_succ]; abel
      rw [this, map_add, ih, hdφ]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have : g m - g n = -∑ k ∈ Finset.Ico m n, d k := by
      rw [Finset.sum_Ico_eq_sub _ hmn]; simp only [hg]; abel
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdmem k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g hgc
  refine ⟨φ L, fun n => ?_⟩
  have h1 := (hL n).map φ
  rw [hgφ, ← himg n] at h1
  exact h1

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := by
  have hsm : ∀ (K : Ideal R) (x : R), x ∈ (K • (⊤ : Submodule R R)) ↔ x ∈ K := by
    intro K x
    simp [smul_eq_mul, Ideal.mul_top]
  have he' : I ^ (e + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ e)) he
  have hpow : ∀ k, I ^ ((e + 1) * k) ≤ J ^ k := by
    intro k
    rw [pow_mul]
    exact Ideal.pow_right_mono he' k
  refine ⟨fun {f} hf => ?_⟩
  have hgc : ∀ {m n : ℕ}, m ≤ n →
      f ((e + 1) * m) ≡ f ((e + 1) * n) [SMOD (J ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
    rw [SModEq.sub_mem, hsm] at h ⊢
    exact hpow m h
  obtain ⟨L, hL⟩ := hJ.prec' (fun k => f ((e + 1) * k)) hgc
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
  have h2 := hL n
  rw [SModEq.sub_mem, hsm] at h1 h2 ⊢
  have h3 : f ((e + 1) * n) - L ∈ I ^ n := Ideal.pow_right_mono hJI n h2
  have := Ideal.add_mem _ h1 h3
  simpa using this

theorem UpperTheory.V.Alg.co_finite :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'] [IsLocalRing R'],
      (∀ x : R', ∃ a : O, x - algebraMap O R' a ∈ maximalIdeal R') → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ _ _ _ hres
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsNoetherian R R' := inferInstance
  haveI hN : IsNoetherianRing R' := isNoetherian_of_tower R this
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI hcompl : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hcomap : ∀ P : Ideal R', P.IsPrime → maximalIdeal R ≤ P.comap (algebraMap R R') → P = maximalIdeal R' := by
    intro P hP hle
    have hcm : (P.comap (algebraMap R R')).IsMaximal := by
      have hne : P.comap (algebraMap R R') ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      have : P.comap (algebraMap R R') = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hne) hle
      rw [this]; infer_instance
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P hcm
    exact IsLocalRing.eq_maximalIdeal this
  have hcm' : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal R'))
  have hloc : IsLocalHom (algebraMap R R') := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [← hcm', Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  set J : Ideal R' := (maximalIdeal R).map (algebraMap R R') with hJdef
  have hJI : J ≤ maximalIdeal R' := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcm']
  have hrad : maximalIdeal R' ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    rw [hcomap P hPp (Ideal.map_le_iff_le_comap.1 hJP)]
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) R' := isPrecomplete_finite (R := R) (M := R') (maximalIdeal R)
  have hJp : IsPrecomplete J R' := by
    rw [hJdef]
    exact IsPrecomplete.map_algebraMap_iff.2 this
  have hprec : IsPrecomplete (maximalIdeal R') R' := prec_cofinal hJI he hJp
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hlocO : IsLocalHom (algebraMap O R') := by
    rw [IsScalarTower.algebraMap_eq O R R']
    infer_instance
  exact
    { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hprec }
      isLocalHom := hlocO
      res_surj := hres }
