import Mathlib

open Module Submodule

namespace FibreCount

theorem card_fibre {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U) (a : U) (x0 : V)
    (hx0 : φ x0 = a) :
    Nat.card {x : V // φ x = a} = Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  have e : {x : V // φ x = a} ≃ LinearMap.ker φ :=
    { toFun := fun x => ⟨x.1 - x0, by rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
      invFun := fun y => ⟨y.1 + x0, by rw [map_add, LinearMap.mem_ker.mp y.2, zero_add, hx0]⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }
  haveI : Finite V := Module.finite_of_finite K
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]

open Classical in

theorem card_fibre_compl {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (z : Fin k → V) (hz : LinearIndependent K z)
    (a : U) :
    Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      if a ∈ span K (Set.range (fun j => φ (z j))) then
        Fintype.card K ^ finrank K (LinearMap.ker φ) -
          Fintype.card K ^ (k - finrank K (span K (Set.range (fun j => φ (z j)))))
      else Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V

  let ψ : (Fin k → K) →ₗ[K] U :=
    { toFun := fun c => φ (∑ j, c j • z j)
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hψ : LinearMap.range ψ = span K (Set.range (fun j => φ (z j))) := by
    ext u
    rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun c => ?_
    show φ (∑ j, c j • z j) = u ↔ _
    rw [map_sum]
    simp only [map_smul]

  have hin : Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} = Nat.card {c : Fin k → K // ψ c = a} := by
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun c => ⟨∑ j, c.1 j • z j, ?_, c.2⟩) ⟨?_, ?_⟩
    · exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨c.1, rfl⟩
    · intro c d hcd
      have h := congrArg Subtype.val hcd
      simp only at h
      have h0 : ∑ j, (c.1 j - d.1 j) • z j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
      exact Subtype.ext (funext fun j => sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hz _ h0 j))
    · intro x
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp x.2.1
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      show φ (∑ j, c j • z j) = a
      rw [hc]; exact x.2.2

  have hsplit : Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      Nat.card {x : V // φ x = a} - Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} := by
    have e : {x : V // φ x = a} ≃
        {x : V // x ∈ span K (Set.range z) ∧ φ x = a} ⊕ {x : V // x ∉ span K (Set.range z) ∧ φ x = a} :=
      { toFun := fun x => if h : x.1 ∈ span K (Set.range z) then Sum.inl ⟨x.1, h, x.2⟩
          else Sum.inr ⟨x.1, h, x.2⟩
        invFun := fun s => Sum.elim (fun y => ⟨y.1, y.2.2⟩) (fun y => ⟨y.1, y.2.2⟩) s
        left_inv := fun x => by
          by_cases h : x.1 ∈ span K (Set.range z) <;> simp [h]
        right_inv := fun s => by
          rcases s with y | y <;> simp [y.2.1] }
    have h := Nat.card_congr e
    rw [Nat.card_sum] at h
    omega
  obtain ⟨x0, hx0⟩ := hφ a
  rw [hsplit, card_fibre φ a x0 hx0, hin]
  split_ifs with ha
  · rw [← hψ] at ha
    obtain ⟨c0, hc0⟩ := ha
    rw [card_fibre ψ a c0 hc0]
    congr 2
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    rw [Module.finrank_fin_fun, hψ] at hrk
    omega
  · have h0 : Nat.card {c : Fin k → K // ψ c = a} = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun c => ha ?_⟩
      rw [← hψ]
      exact ⟨c.1, c.2⟩
    rw [h0, Nat.sub_zero]

theorem fiber_card {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (g : Fin k → U) :
    Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
      Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
        Module.finrank K (LinearMap.ker φ)) *
      ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
        (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  induction k with
  | zero =>
    have h1 : Nat.card {z : Fin 0 → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩⟩⟩
    rw [h1, Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    simp
  | succ k ih =>
    set gk : Fin k → U := fun j => g (Fin.castSucc j) with hgk
    set e := Module.finrank K (LinearMap.ker φ) with he
    set r := Module.finrank K (span K (Set.range gk)) with hr
    set q := Fintype.card K with hq
    have hstep : ∀ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
        Nat.card {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} =
          if g (Fin.last k) ∈ span K (Set.range gk) then q ^ e - q ^ (k - r) else q ^ e := by
      intro z'
      have h := card_fibre_compl φ hφ z'.1 z'.2.1 (g (Fin.last k))
      have hfz : (fun j => φ (z'.1 j)) = gk := funext z'.2.2
      rw [hfz] at h
      exact h
    have hequiv : {z : Fin (k + 1) → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} ≃
        Σ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
          {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} :=
      { toFun := fun z =>
          have hs := linearIndependent_fin_snoc.mp (by rw [Fin.snoc_init_self]; exact z.2.1)
          ⟨⟨Fin.init z.1, hs.1, fun j => z.2.2 _⟩, ⟨z.1 (Fin.last k), hs.2, z.2.2 _⟩⟩
        invFun := fun p => ⟨Fin.snoc p.1.1 p.2.1, linearIndependent_fin_snoc.mpr ⟨p.1.2.1, p.2.2.1⟩,
          fun j => by
            refine Fin.lastCases ?_ (fun i => ?_) j
            · rw [Fin.snoc_last]; exact p.2.2.2
            · rw [Fin.snoc_castSucc]; exact p.1.2.2 i⟩
        left_inv := fun z => Subtype.ext (Fin.snoc_init_self z.1)
        right_inv := fun p => by
          rcases p with ⟨⟨z', h1, h2⟩, ⟨x, h3, h4⟩⟩
          simp [Fin.init_snoc, Fin.snoc_last]
          exact (Subtype.heq_iff_coe_eq (fun y => by simp [Fin.init_snoc])).mpr rfl }
    rw [Nat.card_congr hequiv, Nat.card_sigma, Finset.sum_congr rfl (fun z' _ => hstep z'),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, ih gk]

    have hrange : Set.range g = insert (g (Fin.last k)) (Set.range gk) := by
      ext u
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨j, rfl⟩
        refine Fin.lastCases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) j
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    have hle : r ≤ k := by
      rw [hr]
      exact (finrank_span_le_card (Set.range gk)).trans
        (by simp only [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp))
    split_ifs with hmem
    · have hspan : span K (Set.range g) = span K (Set.range gk) := by
        rw [hrange, Submodule.span_insert_eq_span hmem]
      rw [hspan, ← hr, show k + 1 - r = (k - r) + 1 by omega, Finset.prod_range_succ]
      ring
    · have hspan : Module.finrank K (span K (Set.range g)) = r + 1 := by
        rw [hrange, Submodule.span_insert]
        haveI : FiniteDimensional K (span K (Set.range gk)) :=
          FiniteDimensional.span_of_finite K (Set.finite_range _)
        have hx0 : g (Fin.last k) ≠ 0 := fun h0 => hmem (h0 ▸ Submodule.zero_mem _)
        have hdis : span K {g (Fin.last k)} ⊓ span K (Set.range gk) = ⊥ := by
          rw [inf_comm, ← disjoint_iff]
          exact (Submodule.disjoint_span_singleton' hx0).mpr hmem
        have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {g (Fin.last k)})
          (span K (Set.range gk))
        rw [hdis, finrank_bot, finrank_span_singleton hx0] at h
        omega
      rw [hspan, show k + 1 - (r + 1) = k - r by omega, ← hr]
      ring

end FibreCount
