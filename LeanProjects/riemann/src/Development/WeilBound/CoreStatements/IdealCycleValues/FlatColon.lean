import Mathlib

namespace BaseChangeColon.BC

open MvPolynomial

theorem flat_colon {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (I : Ideal R) (x : R) :
    (I.map (algebraMap R R')).colon {algebraMap R R' x} = (I.colon {x}).map (algebraMap R R') := by
  apply le_antisymm
  · intro g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg
    obtain ⟨n, c, t, ht⟩ := Submodule.mem_span_set'.1 hg
    choose j hj hj' using fun i => (t i).2
    have hrel : ∑ o : Option (Fin n), (o.elim x fun i => -j i) • (o.elim g c : R') = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim, Algebra.smul_def, map_neg, neg_mul, Finset.sum_neg_distrib]
      rw [mul_comm, ← ht, add_neg_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hj', smul_eq_mul, mul_comm]
    obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := R')
      (f := fun o : Option (Fin n) => o.elim x fun i => -j i) (x := fun o => o.elim g c) hrel
    have hg' : g = ∑ l, a none l • y l := h1 none
    rw [hg']
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have h3 := h2 l
    rw [Fintype.sum_option] at h3
    simp only [Option.elim, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at h3
    rw [mul_comm, h3]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hj i)
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ hy

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem map_colon {O O' σ : Type} [CommRing O] [CommRing O'] [Algebra O O'] [Module.Flat O O']
    (I : Ideal (MvPolynomial σ O)) (x : MvPolynomial σ O) :
    (I.map (MvPolynomial.map (algebraMap O O'))).colon {MvPolynomial.map (algebraMap O O') x} =
      (I.colon {x}).map (MvPolynomial.map (algebraMap O O')) := by
  have hb := (inferInstance :
    Algebra.IsPushout O (MvPolynomial σ O) O' (MvPolynomial σ O')).out
  haveI : Module.Flat (MvPolynomial σ O) (MvPolynomial σ O') :=
    Module.Flat.isBaseChange O (MvPolynomial σ O) O' (MvPolynomial σ O') hb
  exact flat_colon (R' := MvPolynomial σ O') I x

theorem ram_colon {O O' σ : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Algebra O O'] (ϖ : O)
    (hm : (Ideal.span {ϖ}).IsMaximal) (ϖ' : O') (h0 : ϖ' ≠ 0) (u : O'ˣ) (e k : ℕ)
    (he : algebraMap O O' ϖ = u * ϖ' ^ e) (hk : k < e) (J : Ideal (MvPolynomial σ O))
    (hJ : C ϖ ∈ J) (g : MvPolynomial σ O')
    (hg : C ϖ' ^ k * g ∈ J.map (MvPolynomial.map (algebraMap O O'))) :
    g ∈ J.map (MvPolynomial.map (algebraMap O O')) ⊔ Ideal.span {C ϖ'} := by
  classical
  set J' := J.map (MvPolynomial.map (algebraMap O O')) with hJ'
  set m : Ideal O := Ideal.span {ϖ} with hmdef
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  have hle : m ≤ J.comap (algebraMap O (MvPolynomial σ O)) := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hJ
  letI : Algebra (O ⧸ m) (MvPolynomial σ O ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (O ⧸ m) (MvPolynomial σ O ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι (O ⧸ m) (MvPolynomial σ O ⧸ J)) :=
    ⟨_, ⟨Module.Basis.ofVectorSpace _ _⟩⟩
  have hb := (inferInstance :
    Algebra.IsPushout O O' (MvPolynomial σ O) (MvPolynomial σ O')).out
  set m' : Ideal O' := Ideal.span {algebraMap O O' ϖ} with hm'
  have hle' : m ≤ m'.comap (Algebra.ofId O O') := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self _
  let ι0 : (O ⧸ m) →ₐ[O] (O' ⧸ m') := Ideal.quotientMapₐ m' (Algebra.ofId O O') hle'
  let lam : ι → (MvPolynomial σ O →ₗ[O] (O' ⧸ m')) := fun i =>
    ι0.toLinearMap ∘ₗ ((b.coord i).restrictScalars O) ∘ₗ (Ideal.Quotient.mkₐ O J).toLinearMap
  have hlam : ∀ i s, lam i s = ι0 (b.coord i (Ideal.Quotient.mk J s)) := fun _ _ => rfl
  let Λ : ι → (MvPolynomial σ O' →ₗ[O'] (O' ⧸ m')) := fun i => hb.lift (lam i)
  have hΛ : ∀ i s, Λ i (MvPolynomial.map (algebraMap O O') s) = lam i s := fun i s =>
    hb.lift_eq (lam i) s
  have hkill : ∀ i, ∀ w ∈ J', Λ i w = 0 := by
    intro i w hw
    suffices h : ∀ h, Λ i (h * w) = 0 by simpa using h 1
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro h
      induction h using hb.inductionOn with
      | zero => simp
      | tmul t =>
        change Λ i (MvPolynomial.map (algebraMap O O') t * _) = 0
        rw [← map_mul, hΛ, hlam, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left t hs)]
        simp
      | smul a t ht => rw [smul_mul_assoc, map_smul, ht, smul_zero]
      | add a t ha ht => rw [add_mul, map_add, ha, ht, add_zero]
    | zero => simp
    | add x y _ _ hx hy => intro h; rw [mul_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => intro h; rw [smul_eq_mul, ← mul_assoc, hx]
  choose B hB using fun i => Ideal.Quotient.mk_surjective (I := J) (b i)
  let U : Submodule O' (MvPolynomial σ O') :=
    Submodule.span O' (Set.range fun i => MvPolynomial.map (algebraMap O O') (B i)) ⊔
      J'.restrictScalars O'
  have hJU : ∀ s ∈ J, MvPolynomial.map (algebraMap O O') s ∈ U := fun s hs =>
    Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hs)
  have hU1 : ∀ x ∈ Submodule.span (O ⧸ m) (Set.range b), ∀ s, Ideal.Quotient.mk J s = x →
      MvPolynomial.map (algebraMap O O') s ∈ U := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro s hs
      have h1 := hJU _ (Ideal.Quotient.eq.1 (hs.trans (hB i).symm))
      have h2 : MvPolynomial.map (algebraMap O O') (B i) ∈ U :=
        Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      simpa using U.add_mem h1 h2
    | zero => exact fun s hs => hJU s (Ideal.Quotient.eq_zero_iff_mem.1 hs)
    | add x y _ _ hx hy =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 := hx s1 rfl
      have h2 := hy (s - s1) (by rw [map_sub, hs, add_sub_cancel_left])
      simpa using U.add_mem h1 h2
    | smul c x _ hx =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective c
      have h1 := U.smul_mem (algebraMap O O' o) (hx s1 rfl)
      have h3 : Ideal.Quotient.mk J s = Ideal.Quotient.mk J (C o * s1) := by
        rw [hs, Algebra.smul_def, map_mul]
        rfl
      have h2 := hJU _ (Ideal.Quotient.eq.1 h3)
      rw [smul_eq_C_mul] at h1
      simpa using U.add_mem h1 h2
  have hU : ∀ w, w ∈ U := by
    intro w
    induction w using hb.inductionOn with
    | zero => exact U.zero_mem
    | tmul t => exact hU1 _ (by rw [b.span_eq]; trivial) t rfl
    | smul a t ht => exact U.smul_mem a ht
    | add a t ha ht => exact U.add_mem ha ht
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 (hU g)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left hw)
  refine Ideal.sum_mem _ fun i hi => ?_
  have h1 := hkill i _ hg
  rw [← C_pow, ← smul_eq_C_mul, map_smul, map_add, hkill i w hw, add_zero, Finsupp.sum, map_sum,
    Finset.sum_eq_single i] at h1
  · rw [map_smul, hΛ, hlam, hB] at h1
    have h2 : Ideal.Quotient.mk m' (ϖ' ^ k * c i) = 0 := by
      rw [← h1]
      simp [Algebra.smul_def]
    rw [Ideal.Quotient.eq_zero_iff_mem, hm', Ideal.mem_span_singleton', he] at h2
    obtain ⟨z, hz⟩ := h2
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have h3 : c i = ϖ' * (z * u * ϖ' ^ r) := by
      apply mul_left_cancel₀ (pow_ne_zero k h0)
      rw [← hz]; ring
    change c i • _ ∈ _
    rw [h3, smul_eq_C_mul, C_mul, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro l _ hl
    rw [map_smul, hΛ, hlam, hB]
    simp [hl]
  · exact fun h => absurd hi h

end BaseChangeColon.BC
