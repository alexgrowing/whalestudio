import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Dual

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem vLE_ne_zero' {κ : KK O} {D : ℝ} (h : vLE p κ D) : κ ≠ 0 := by
  rintro rfl
  obtain ⟨q, hq, -⟩ := h
  rw [valuation_zero_alt] at hq
  exact WithTop.top_ne_coe hq

theorem nv_irr' {w : O} (hw : Irreducible w) : dvrOrderNat w = 1 := by
  simp [dvrOrderNat, IsDiscreteValuationRing.addVal_uniformizer hw]

theorem vK_int_form (x : KK O) (hx : x ≠ 0) : ∃ k : ℤ, vK p x = (((k : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  unfold vK ordW
  rw [if_neg hx]
  exact ⟨_, rfl⟩

theorem vK_le_zero_of_not_int (S : UniformizedDVR p O) (a : KK O)
    (h : ¬ (0 : WithTop ℚ) ≤ vK p (a * (algebraMap O (KK O) S.w)⁻¹)) :
    ∃ q : ℚ, vK p a = (q : WithTop ℚ) ∧ q ≤ 0 := by
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hepos : (0 : ℚ) < ramE p O := by
    have := ramification_index_ne_zero S
    exact_mod_cast Nat.pos_of_ne_zero this
  have ha : a ≠ 0 := by
    rintro rfl
    apply h
    rw [zero_mul, valuation_zero_alt]
    exact le_top
  obtain ⟨k, hk⟩ := vK_int_form a ha
  have hwinv : vK p ((algebraMap O (KK O) S.w)⁻¹) =
      (((-1 : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
    rw [valuation_eq_of_fraction p _ 1 S.w one_ne_zero hw0 (by rw [inv_mul_cancel₀ hw0', map_one]),
      nv_irr' S.w_irr]
    simp [dvrOrderNat]
  rw [valuation_mul_alt, hk, hwinv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  push_neg at h
  refine ⟨(k : ℚ) / (ramE p O : ℚ), hk, ?_⟩
  have h2 : ((k : ℚ) - 1) / (ramE p O : ℚ) < 0 := by
    rw [sub_div]
    rw [neg_div] at h
    linarith
  have h3 : (k : ℚ) - 1 < 0 := by
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (div_nonneg hc hepos.le))
  have h4 : k < 1 := by exact_mod_cast (by linarith : (k : ℚ) < 1)
  have h5 : (k : ℚ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
  exact div_nonpos_of_nonpos_of_nonneg h5 hepos.le

theorem be_sum_left (be : V → V → KK O) (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v) {n : ℕ} (a : Fin n → KK O) (x : Fin n → V) (v : V) :
    be (∑ i, a i • x i) v = ∑ i, a i * be (x i) v := by
  classical
  have h0 : be 0 v = 0 := by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [h0]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]

theorem goodSub_of_dual (S : UniformizedDVR p O) (be : V → V → KK O)
    (hsm : ∀ (a : KK O) (u v : V), be (a • u) v = a * be u v)
    (hadd : ∀ u u' v, be (u + u') v = be u v + be u' v)
    (L : Submodule O V) {n : ℕ} (x y : Fin n → V) (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L)
    (c : KK O) (hxy : ∀ i j, be (x i) (y j) = if i = j then c else 0) (D : ℝ) (hc : vLE p c D) :
    ∃ L₂ : Submodule O V, GoodSub p be L L₂ D ∧ n ≤ Module.finrank O L₂ := by
  classical
  have hc0 : c ≠ 0 := vLE_ne_zero' hc
  have hw0 : S.w ≠ 0 := S.w_irr.ne_zero
  have hw0' : algebraMap O (KK O) S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hw0
  have hbe0 : ∀ v, be 0 v = 0 := fun v => by
    have := hsm 0 0 v
    rwa [zero_smul, zero_mul] at this
  have hsum : ∀ (t : Fin n → KK O) (j : Fin n), be (∑ i, t i • x i) (y j) = t j * c := by
    intro t j
    rw [be_sum_left be hsm hadd t x (y j)]
    simp [hxy]
  have hspan : ∀ s : Fin n → O,
      (∑ i, s i • x i) ∈ (Submodule.span (KK O) (Set.range x)).restrictScalars O := by
    intro s
    rw [Submodule.restrictScalars_mem]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (KK O) (s i) (x i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O, ⟨⟨inf_le_left, ?_⟩, ?_⟩, ?_⟩
  · intro o u ho hu hou
    refine Submodule.mem_inf.2 ⟨hu, ?_⟩
    have h2 := (Submodule.mem_inf.1 hou).2
    rw [Submodule.restrictScalars_mem] at h2 ⊢
    have ho' : algebraMap O (KK O) o ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ho
    have hu' : u = (algebraMap O (KK O) o)⁻¹ • (o • u) := by
      rw [← algebraMap_smul (KK O) o u, smul_smul, inv_mul_cancel₀ ho', one_smul]
    rw [hu']
    exact Submodule.smul_mem _ _ h2
  · rintro u ⟨hu, hprim⟩
    obtain ⟨hul, huw⟩ := Submodule.mem_inf.1 hu
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
    obtain ⟨t, rfl⟩ := huw
    by_cases hall : ∀ j, 0 ≤ vK p (t j * (algebraMap O (KK O) S.w)⁻¹)
    · exfalso
      choose s hs using fun j => (valuation_nonneg_iff_integral S _).1 (hall j)
      have ht : ∀ j, t j = algebraMap O (KK O) S.w * algebraMap O (KK O) (s j) := by
        intro j
        rw [← hs j, mul_comm (t j), ← mul_assoc, mul_inv_cancel₀ hw0', one_mul]
      have hx' : (∑ i, s i • x i) ∈ L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :=
        Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i), hspan s⟩
      have hu' : (∑ i, t i • x i) = S.w • ∑ i, s i • x i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [ht i, mul_smul, algebraMap_smul, algebraMap_smul]
      exact S.w_irr.not_isUnit (hprim S.w _ hx' hu')
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨q, hq, hq0⟩ := vK_le_zero_of_not_int S (t j) (not_le.2 hj)
      obtain ⟨qc, hqc, hqcD⟩ := hc
      have hq0' : (q : ℝ) ≤ 0 := by exact_mod_cast hq0
      refine ⟨y j, hy j, q + qc, ?_, ?_⟩
      · rw [hsum, valuation_mul_alt, hq, hqc, ← WithTop.coe_add]
      · push_cast
        linarith
  · have hli : LinearIndependent (KK O) x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := hsum g i
      rw [hg, hbe0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hc0
    have hliO : LinearIndependent O x := (LinearIndependent.iff_fractionRing O (KK O)).2 hli
    let f : Fin n → (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) :=
      fun i => ⟨x i, Submodule.mem_inf.2 ⟨hx i, by
        rw [Submodule.restrictScalars_mem]
        exact Submodule.subset_span ⟨i, rfl⟩⟩⟩
    have hf : LinearIndependent O f :=
      LinearIndependent.of_comp (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O).subtype hliO
    let φ : (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) →ₗ[O]
        (Fin n → KK O) :=
      { toFun := fun u j => be u (y j)
        map_add' := fun u u' => by
          funext j
          exact hadd _ _ _
        map_smul' := fun o u => by
          funext j
          simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
          rw [← algebraMap_smul (KK O) o (u : V), hsm, Algebra.smul_def] }
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      obtain ⟨-, huw⟩ := Submodule.mem_inf.1 u.2
      rw [Submodule.restrictScalars_mem, Submodule.mem_span_range_iff_exists_fun] at huw
      obtain ⟨t, ht⟩ := huw
      have ht0 : ∀ j, t j = 0 := fun j => by
        have h1 := congrFun hu j
        have h2 := hsum t j
        rw [ht] at h2
        change be (u : V) (y j) = 0 at h1
        rw [h1] at h2
        exact (mul_eq_zero.1 h2.symm).resolve_right hc0
      ext
      rw [← ht]
      simp [ht0]
    have hup : Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
        Submodule O V) ≤ n := by
      calc Module.rank O (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O :
            Submodule O V)
          ≤ Module.rank O (Fin n → KK O) := LinearMap.rank_le_of_injective φ hφ
        _ = Module.rank (KK O) (Fin n → KK O) :=
          (IsFractionRing.rank_right_eq (R := O) (S := KK O) (N := Fin n → KK O)).symm
        _ = n := by simp
    have hlow : (n : Cardinal) ≤ Module.rank O
        (L ⊓ (Submodule.span (KK O) (Set.range x)).restrictScalars O : Submodule O V) := by
      simpa using hf.cardinal_le_rank
    rw [Module.finrank_eq_of_rank_eq (le_antisymm hup hlow)]

end Dual

end Formalism.MainNotions.G.SymmetricFormBlocks

end
