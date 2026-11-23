import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem zl_pow {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (u : R) (hu : u - 1 ∈ I)
    (N : ℕ) : u ^ l ^ N - 1 ∈ I ^ (N + 1) := by
  induction N with
  | zero => simpa using hu
  | succ N ih =>
    have h1 : u ^ l ^ N - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero N) ih
    rw [pow_succ l, pow_mul, ← mul_geom_sum, pow_succ I]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1
    simp only [map_sum, map_pow _ (u ^ l ^ N), h1, one_pow]
    simpa using hl

private theorem zl_eq {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {a b : R}
    (h : ∀ n, Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact Ideal.Quotient.eq.1 (h n))

private theorem zl_lc (l : ℕ) [Fact l.Prime] (N : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow N : ℤ_[l] → ZMod (l ^ N)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

private theorem zl_one (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (hl : (l : R) ∈ I) (u : Rˣ) (hu : (u : R) - 1 ∈ I) :
    ∃ χ : Multiplicative ℤ_[l] →* Rˣ, AdicCont I (fun x => ((χ x : Rˣ) : R)) ∧ χ (Multiplicative.ofAdd 1) = u := by
  have hl0 : ∀ N, NeZero (l ^ N) := fun N => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hB : ∀ N (a b : ℕ), (a : ZMod (l ^ N)) = b →
      Ideal.Quotient.mk (I ^ N) (u ^ a) = Ideal.Quotient.mk (I ^ N) (u ^ b) := fun N a b h => by
    rw [map_pow, map_pow]
    refine pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) ?_
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (I ^ N)), Ideal.Quotient.eq]
    exact Ideal.pow_le_pow_right (Nat.le_succ N) (zl_pow I l hl u hu N)
  have hex : ∀ s : ℤ_[l], ∃ y : R, ∀ N (k : ℕ), (k : ZMod (l ^ N)) = PadicInt.toZModPow N s →
      Ideal.Quotient.mk (I ^ N) y = Ideal.Quotient.mk (I ^ N) (u ^ k) := fun s => by
    obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) (fun n => (u : R) ^ (PadicInt.toZModPow n s).val)
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
        refine hB _ _ _ ?_
        rw [ZMod.natCast_zmod_val, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ hmn])
    refine ⟨y, fun N k hk => ?_⟩
    have := (hy N).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq] at this
    rw [this]
    exact hB _ _ _ (by rw [ZMod.natCast_zmod_val, hk])
  choose p hp using hex
  let P : Multiplicative ℤ_[l] →* R :=
    { toFun := fun x => p x.toAdd
      map_one' := zl_eq I fun n => by simpa using hp 0 n 0 (by simp)
      map_mul' := fun a b => zl_eq I fun n => by
        rw [toAdd_mul, map_mul (Ideal.Quotient.mk (I ^ n)), hp (_ + _) n _ (ZMod.natCast_zmod_val _), hp a.toAdd n _ (ZMod.natCast_zmod_val _),
          hp b.toAdd n _ (ZMod.natCast_zmod_val _), ← map_mul, ← pow_add]
        exact hB _ _ _ (by simp) }
  refine ⟨P.toHomUnits, fun N => ?_, Units.ext (zl_eq I fun n => ?_)⟩
  · have : (fun g : Multiplicative ℤ_[l] => Ideal.Quotient.mk (I ^ N) ((P.toHomUnits g : Rˣ) : R)) =
        (fun z : ZMod (l ^ N) => Ideal.Quotient.mk (I ^ N) ((u : R) ^ z.val)) ∘
          ((PadicInt.toZModPow N : ℤ_[l] → ZMod (l ^ N)) ∘ Multiplicative.toAdd) :=
      funext fun g => hp _ N _ (ZMod.natCast_zmod_val _)
    rw [this]
    exact ((zl_lc l N).comp_continuous continuous_toAdd).comp _
  · have := hp 1 n 1 (by simp)
    rw [pow_one] at this
    exact this

theorem UpperTheory.V.W.lam_zl :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → Rˣ), (∀ i, res O R (u i) = 1) →
      ∃! χ : Multiplicative (ι → ℤ_[l]) →* Rˣ, AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ ∀ i, χ (Multiplicative.ofAdd (Pi.single i 1)) = u i := by
  intro l _ O _ _ _ R _ _ _ ι _ _ u hu
  have hl : (l : R) ∈ maximalIdeal R := (res_eq_zero_iff O R _).1 (by rw [map_natCast, CharP.cast_eq_zero])
  have hu' : ∀ i, (u i : R) - 1 ∈ maximalIdeal R := fun i =>
    (res_eq_zero_iff O R _).1 (by rw [map_sub, hu, map_one, sub_self])
  choose c hc hc1 using fun i => zl_one l (maximalIdeal R) hl (u i) (hu' i)
  refine existsUnique_of_exists_of_unique ⟨?_, ?_, ?_⟩ ?_
  · exact
      { toFun := fun x => ∏ i, c i (Multiplicative.ofAdd (x.toAdd i))
        map_one' := by simp
        map_mul' := fun a b => by simp [ofAdd_add, Finset.prod_mul_distrib] }
  · intro N
    letI : TopologicalSpace (R ⧸ maximalIdeal R ^ N) := ⊥
    haveI : DiscreteTopology (R ⧸ maximalIdeal R ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod]
    refine continuous_finset_prod _ fun i _ => ?_
    exact (hc i N).continuous.comp (continuous_ofAdd.comp ((continuous_apply i).comp continuous_toAdd))
  · intro i
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [Finset.prod_eq_single i, Pi.single_eq_same, hc1]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, ofAdd_zero, map_one]
    · simp
  · rintro χ χ' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine MonoidHom.ext fun x => Units.ext (zl_eq (maximalIdeal R) fun N => ?_)
    letI : TopologicalSpace (R ⧸ maximalIdeal R ^ N) := ⊥
    haveI : DiscreteTopology (R ⧸ maximalIdeal R ^ N) := ⟨rfl⟩
    have hd : DenseRange (Pi.map fun (_ : ι) => (Nat.cast : ℕ → ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_natCast
    have key := hd.equalizer ((h1 N).continuous.comp continuous_ofAdd) ((h1' N).continuous.comp continuous_ofAdd)
      (funext fun n => by
        have e : Multiplicative.ofAdd (Pi.map (fun (_ : ι) => (Nat.cast : ℕ → ℤ_[l])) n) =
            ∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ_[l]) : ι → ℤ_[l]) ^ n i := by
          apply Multiplicative.toAdd.injective
          funext j
          simp [toAdd_prod, Finset.sum_apply, Pi.single_apply]
        simp only [Function.comp_apply, e, map_prod, map_pow, h2, h2'])
    exact congrFun key x.toAdd
