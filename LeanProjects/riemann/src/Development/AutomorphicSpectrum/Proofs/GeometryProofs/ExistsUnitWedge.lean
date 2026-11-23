import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

theorem wedge_rows {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

theorem wedge_ne_zero {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent Ω v) : exteriorPower.ιMulti Ω n v ≠ 0 := by
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding
  have hs : exteriorPower.ιMulti_family Ω n v s = exteriorPower.ιMulti Ω n v := by
    simp only [exteriorPower.ιMulti_family, s, Equiv.symm_apply_apply]
    rfl
  exact hs ▸ hfam.ne_zero s

theorem exists_unit_wedge {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (ω : ⋀[Ω]^p E) (hω : ω ≠ 0)
    (H : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {ω}) :
    ∃ (b : Fin p → E) (r : R), (∀ i, b i ∈ A) ∧ IsUnit r ∧
      exteriorPower.ιMulti Ω p b = (r : Ω) • ω := by
  by_contra hcon
  push_neg at hcon
  let N : Submodule R (⋀[Ω]^p E) :=
    Submodule.map (LinearMap.toSpanSingleton R (⋀[Ω]^p E) ω) (IsLocalRing.maximalIdeal R)
  have hle : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have hmem : exteriorPower.ιMulti Ω p b ∈ Submodule.span R {ω} :=
      H ▸ Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
    have hnu : ¬ IsUnit r := fun hu => hcon b r hb hu hr.symm
    exact ⟨r, (IsLocalRing.mem_maximalIdeal r).2 hnu, by simpa using hr⟩
  have hωN : ω ∈ N := hle (H ▸ Submodule.mem_span_singleton_self ω)
  obtain ⟨r, hr, hrω⟩ := hωN
  have hrω' : (r : Ω) • ω = ω := hrω
  have h1 : (r : Ω) = 1 := by
    have h0 : ((r : Ω) - 1) • ω = 0 := by rw [sub_smul, one_smul, hrω', sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hω
  have hr1 : r = 1 := Subtype.ext h1
  rw [hr1] at hr
  exact ((IsLocalRing.mem_maximalIdeal (1 : R)).1 hr) isUnit_one

theorem wedge_update_sum {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {p : ℕ}
    (b : Fin p → E) (c : Fin p → Ω) (j : Fin p) :
    exteriorPower.ιMulti Ω p (Function.update b j (∑ k, c k • b k)) =
      c j • exteriorPower.ιMulti Ω p b := by
  rw [AlternatingMap.map_update_sum, Finset.sum_eq_single j]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  · intro k _ hk
    rw [AlternatingMap.map_update_smul, AlternatingMap.map_update_self _ _ hk.symm, smul_zero]
  · simp

theorem wedge_frame : ∀ (Ω E : Type) [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (v : Fin p → E) (α : Ω),
    LinearIndependent Ω v → (∀ y ∈ A, y ∈ Submodule.span Ω (Set.range v)) → α ≠ 0 →
    Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {α • exteriorPower.ιMulti Ω p v} →
    ∃ P : Matrix (Fin p) (Fin p) Ω, LinearIndependent Ω (fun i => ∑ j, P i j • v j) ∧
      A = Submodule.span R (Set.range fun i => ∑ j, P i j • v j) ∧
      ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ P.det = c * α := by
  intro Ω E _ _ _ R _ A p v α hv hA hα H
  have hιv := wedge_ne_zero v hv
  have hω : α • exteriorPower.ιMulti Ω p v ≠ 0 := smul_ne_zero hα hιv
  obtain ⟨b, r, hb, hu, hιb⟩ := exists_unit_wedge R A p _ hω H
  obtain ⟨u, rfl⟩ := hu
  have hc0 : ((u : R) : Ω) ≠ 0 := by
    intro h0
    exact u.ne_zero (Subtype.ext h0)
  have hcinv : ((u : R) : Ω)⁻¹ = (((u⁻¹ : Rˣ) : R) : Ω) := by
    have h : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hιb0 : exteriorPower.ιMulti Ω p b ≠ 0 := by
    rw [hιb]; exact smul_ne_zero hc0 hω
  have hbli : LinearIndependent Ω b := by
    by_contra hnot
    exact hιb0 (AlternatingMap.map_linearDependent _ _ hnot)
  have hex : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hA _ (hb i))
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin p) (Fin p) Ω, ∀ i, ∑ j, P i j • v j = b i :=
    ⟨Matrix.of fun i => (hex i).choose, fun i => (hex i).choose_spec⟩
  have hPb : (fun i => ∑ j, P i j • v j) = b := funext hP
  have hdet : P.det = ((u : R) : Ω) * α := by
    have h1 := wedge_rows P v
    rw [hPb, hιb, smul_smul] at h1
    exact (smul_left_injective Ω hιv h1).symm
  refine ⟨P, ?_, ?_, (u : R), (u : R).2, hcinv ▸ ((u⁻¹ : Rˣ) : R).2, hc0, hdet⟩
  · rw [hPb]; exact hbli
  · rw [hPb]
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro y hy
      have hspan : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range v) := by
        haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range v)) :=
          FiniteDimensional.span_of_finite Ω (Set.finite_range v)
        refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
        · rintro _ ⟨i, rfl⟩
          exact hA _ (hb i)
        · rw [finrank_span_eq_card hbli, finrank_span_eq_card hv]
      have hy' : y ∈ Submodule.span Ω (Set.range b) := hspan ▸ hA y hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hy'
      have hcR : ∀ j, c j ∈ R := by
        intro j
        have hmem : exteriorPower.ιMulti Ω p (Function.update b j y) ∈
            Submodule.span R {α • exteriorPower.ιMulti Ω p v} := by
          rw [← H]
          refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
          by_cases hij : i = j
          · subst hij; simpa using hy
          · simpa [Function.update_of_ne hij] using hb i
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
        rw [← hc, wedge_update_sum, hιb] at hs
        have hs' : (s : Ω) • (α • exteriorPower.ιMulti Ω p v) =
            (c j * ((u : R) : Ω)) • (α • exteriorPower.ιMulti Ω p v) := by
          rw [mul_smul]; exact hs
        have hsc : (s : Ω) = c j * ((u : R) : Ω) := smul_left_injective Ω hω hs'
        have hcj : c j = (s : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) := by
          rw [← hcinv, hsc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
        rw [hcj]
        exact R.mul_mem s.2 ((u⁻¹ : Rˣ) : R).2
      rw [← hc]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : c j • b j = (⟨c j, hcR j⟩ : R) • b j := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact hb i

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
