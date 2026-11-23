import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem locAt_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    (A : Submodule (𝓞 L) W) : locAt v (locAt v A) = locAt v A := by
  refine le_antisymm (fun x hx => ?_) (le_locAt v _)
  obtain ⟨s, hs, h⟩ := mem_locAt.1 hx
  obtain ⟨t, ht, h'⟩ := mem_locAt.1 h
  refine mem_locAt.2 ⟨t * s, fun hm => (v.maximalIdeal.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
  rwa [mul_smul]

theorem locAt_mono {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    {A B : Submodule (𝓞 L) W} (h : A ≤ B) : locAt v A ≤ locAt v B := fun x hx => by
  obtain ⟨t, ht, hx⟩ := mem_locAt.1 hx
  exact mem_locAt.2 ⟨t, ht, h hx⟩

theorem finite_not_le_one (a : L) : {w : FinitePlace L | ¬ w a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    refine Set.finite_empty.subset fun w hw => hw ?_
    rw [map_zero]
    exact zero_le_one
  · refine (FinitePlace.mulSupport_finite ha).subset fun w hw => ?_
    intro h
    exact hw (le_of_eq h)

theorem exists_mul_le_one {v w : FinitePlace L} (hvw : w ≠ v) (a : L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ w ((t : L) * a) ≤ 1 := by
  have hne : w.maximalIdeal.asIdeal ≠ v.maximalIdeal.asIdeal := fun h =>
    hvw (FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h))
  have hnle : ¬ w.maximalIdeal.asIdeal ≤ v.maximalIdeal.asIdeal := fun h =>
    hne (w.maximalIdeal.isMaximal.eq_of_le v.maximalIdeal.isPrime.ne_top h)
  obtain ⟨p, hpw, hpv⟩ := SetLike.not_le_iff_exists.1 hnle
  have hp0 : (p : L) ≠ 0 := by
    intro h
    have : p = 0 := by exact_mod_cast h
    exact hpv (this ▸ Ideal.zero_mem _)
  have hlt : w (p : L) < 1 := by
    have h1 : w (p : L) ≤ 1 := place_int_le_one w p
    refine lt_of_le_of_ne h1 fun h => ?_
    have h2 := (place_le_one_iff w ((p : L)⁻¹)).1 (by rw [map_inv₀, h, inv_one])
    have h3 : w.maximalIdeal.valuation L (p : L) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hpw
    have h4 : 0 < w.maximalIdeal.valuation L (p : L) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
    rw [map_inv₀, inv_le_one₀ h4] at h2
    exact absurd h3 (not_lt.2 h2)
  by_cases ha : w a = 0
  · exact ⟨1, fun h => v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
      simp [ha]⟩
  · have hapos : 0 < w a := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm ha)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hapos) hlt
    refine ⟨p ^ k, fun h => hpv (v.maximalIdeal.isPrime.mem_of_pow_mem _ h), ?_⟩
    push_cast
    rw [map_mul, map_pow]
    calc w (p : L) ^ k * w a ≤ (w a)⁻¹ * w a := by gcongr
      _ = 1 := inv_mul_cancel₀ ha

theorem exists_smul_mem_locAt_frame {v w : FinitePlace L} (hvw : w ≠ v)
    {T : Matrix (Fin n) (Fin n) L} (hT : T.det ≠ 0) (x : Fin n → L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ locAt w (frame T) := by
  classical
  choose s hs hs' using fun i => exists_mul_le_one hvw ((T⁻¹ *ᵥ x) i)
  refine ⟨∏ i, s i, fun h => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
    exact hs i hi
  · refine mem_locAt_frame.2 ⟨((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x), fun i => ?_, ?_⟩
    · have e : (((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x)) i =
          ((∏ j ∈ Finset.univ.erase i, s j : 𝓞 L) : L) * ((s i : L) * (T⁻¹ *ᵥ x) i) := by
        rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e]
      exact place_mul_le_one w (place_int_le_one w _) (hs' i)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hT),
        Matrix.one_mulVec]
      funext i
      simp [Algebra.smul_def]

theorem finite_notMem_locAt_frame {T : FinitePlace L → Matrix (Fin n) (Fin n) L}
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (x : Fin n → L) :
    {w : FinitePlace L | x ∉ locAt w (frame (T w))}.Finite := by
  refine (hfin.union (Set.finite_iUnion fun i => finite_not_le_one (x i))).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
  apply hw
  rw [hc.1.locAt_frame]
  exact mem_locAt_frame_one.2 hc.2

end SlopeTestRemainingChoices

theorem locAt_glued (L : Type) [Field L] [NumberField L] (n : ℕ)
    (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (hdet : ∀ v, (T v).det ≠ 0)
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (v : FinitePlace L) :
    locAt v (glued T) = locAt v (frame (T v)) := by
  classical
  refine le_antisymm ?_ fun x hx => ?_
  · have h : glued T ≤ locAt v (frame (T v)) := iInf_le _ v
    exact (locAt_mono v h).trans (locAt_locAt v _).le
  · have hone : (1 : 𝓞 L) ∉ v.maximalIdeal.asIdeal := fun h =>
      v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have hex : ∀ w : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧
        (w ≠ v → t • x ∈ locAt w (frame (T w))) := fun w => by
      by_cases hw : w = v
      · exact ⟨1, hone, fun h => absurd hw h⟩
      · obtain ⟨t, ht, h⟩ := exists_smul_mem_locAt_frame hw (hdet w) x
        exact ⟨t, ht, fun _ => h⟩
    choose τ hτ hτ' using hex
    let S : Finset (FinitePlace L) := (finite_notMem_locAt_frame hfin x).toFinset.erase v
    refine mem_locAt.2 ⟨∏ w ∈ S, τ w, fun h => ?_, ?_⟩
    · obtain ⟨w, -, hw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
      exact hτ w hw
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      by_cases hw : w ∈ S
      · rw [← Finset.mul_prod_erase S τ hw, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (hτ' w (Finset.ne_of_mem_erase hw))
      · refine Submodule.smul_mem _ _ ?_
        by_cases hv : w = v
        · rw [hv]; exact hx
        · by_contra hc
          exact hw (Finset.mem_erase.2 ⟨hv, (Set.Finite.mem_toFinset _).2 hc⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
