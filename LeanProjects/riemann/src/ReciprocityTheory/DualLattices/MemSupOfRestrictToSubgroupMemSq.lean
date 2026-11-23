import ReciprocityTheory.DualLattices.MemMapAugmentationIdealComapPullbackQuotient

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem exists_basis_map_restrictToSubgroup (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]
    rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩

theorem exists_coset_basis (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)

theorem mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)

private theorem mem_augIdeal_iff {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal]

theorem mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  intro g hgI hres
  have hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0 := mem_augIdeal_iff _
  have hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier :=
    Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1
  have hle : augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤
      (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨⟨a, ha, rfl⟩, hp0⟩ := (mem_augIdeal_iff _ _).1 hp
    obtain ⟨⟨b, hb, rfl⟩, hq0⟩ := (mem_augIdeal_iff _ _).1 hq
    refine ⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩
    · simpa [resK] using hp0
    · simpa [resK] using hq0
    · funext k; simp [resK]
  obtain ⟨q, hq, hqg⟩ := hle hres
  have hgq : g - q ∈ AA.carrier := AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)
  have hker := mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])
  have hmul : (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
    refine Submodule.mul_le.mpr fun e he a ha => ?_
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨he'A, he'0⟩ := (mem_augIdeal_iff _ _).1 he'
    obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA ha 0
    have heI : pullQ (R := R) K e' ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩
    have haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem),
        by simp [Algebra.smul_def, hr]⟩
    have hsplit : pullQ (R := R) K e' * a =
        pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by
      rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI))
      (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))
  have hg : g = (g - q) + q := by abel
  rw [hg]
  exact Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)

end ReciprocityTheory.PGsh.L2
