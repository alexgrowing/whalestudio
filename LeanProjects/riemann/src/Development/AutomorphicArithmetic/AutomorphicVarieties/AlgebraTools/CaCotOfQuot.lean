import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem card_le_dim (R : Type) [CommRing R] [IsRegularLocalRing R] (r : ℕ) (x : Fin r → R)
    (hx : CotInd R x) : (r : WithBot ℕ∞) ≤ ringKrullDim R := by
  obtain ⟨s, y, -, -, hc⟩ := cotInd_extend R _ x hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc, Fintype.card_fin]
  exact_mod_cast Nat.le_add_right r s

private theorem exists_max (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) :
    ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ (∀ k, x k ∈ I) ∧
      I ≤ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 := by
  classical
  let P : ℕ → Prop := fun r => ∃ x : Fin r → R, CotInd R x ∧ ∀ k, x k ∈ I
  have h0 : P 0 := ⟨Fin.elim0, ⟨fun k => k.elim0, fun _ _ k => k.elim0⟩, fun k => k.elim0⟩
  have hb : ∀ r, P r → r ≤ (maximalIdeal R).spanFinrank := by
    rintro r ⟨x, hx, -⟩
    have := card_le_dim R r x hx
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at this
    exact_mod_cast this
  obtain ⟨x, hx, hxI⟩ : P (Nat.findGreatest P (maximalIdeal R).spanFinrank) :=
    Nat.findGreatest_spec (Nat.zero_le _) h0
  refine ⟨_, x, hx, hxI, fun t ht => ?_⟩
  by_contra hn
  have h1 : P (Nat.findGreatest P (maximalIdeal R).spanFinrank + 1) := by
    refine ⟨Fin.cons t x, ⟨?_, ?_⟩, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact hI ht
      · exact hx.mem j
    · intro a ha
      rw [Fin.sum_univ_succ] at ha
      simp only [Fin.cons_zero, Fin.cons_succ] at ha
      have ha0 : a 0 ∈ maximalIdeal R := by
        by_contra hu
        have hu' : IsUnit (a 0) := by simpa using hu
        apply hn
        rw [← Ideal.unit_mul_mem_iff_mem _ hu']
        have h2 : ∑ i, a i.succ * x i ∈ Ideal.span (Set.range x) :=
          Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
        have h3 := sub_mem (Ideal.mem_sup_right (S := Ideal.span (Set.range x)) ha)
          (Ideal.mem_sup_left h2)
        simpa using h3
      have h4 : a 0 * t ∈ maximalIdeal R ^ 2 := by
        rw [sq]
        exact Ideal.mul_mem_mul ha0 (hI ht)
      have h5 : ∑ i, a i.succ * x i ∈ maximalIdeal R ^ 2 := by
        simpa using sub_mem ha h4
      intro k
      exact Fin.cases ha0 (fun j => hx.indep (fun i => a i.succ) h5 j) k
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ht
      · exact hxI j
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hb _ h1) h1

theorem UpperTheory.V.AlgebraTools.exists_cotInd_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ Ideal.span (Set.range x) = I := by
  intro R _ _ I _
  have hne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hI : I ≤ maximalIdeal R := le_maximalIdeal hne
  obtain ⟨r, x, hx, hxI, hle⟩ := exists_max R I hI
  refine ⟨r, x, hx, ?_⟩
  have hJ : Ideal.span (Set.range x) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hxI k
  obtain ⟨s, y, hxy, -, hc⟩ := cotInd_extend R _ x hx
  obtain ⟨-, hd, hp⟩ := regular_quotient_cotInd R _ x hx
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : CotInd (R ⧸ I) (fun j => Ideal.Quotient.mk I (y j)) := by
    refine ⟨fun j => hmax ▸ Ideal.mem_map_of_mem _ (hxy.mem (Sum.inr j)), fun a ha => ?_⟩
    choose b hb using fun j => Ideal.Quotient.mk_surjective (a j)
    have h1 : Ideal.Quotient.mk I (∑ j, b j * y j) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R ^ 2) := by
      rw [Ideal.map_pow, hmax]
      simpa [hb] using ha
    rw [Ideal.mem_quotient_iff_mem_sup] at h1
    have h2 : ∑ j, b j * y j ∈ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 :=
      sup_le le_sup_right hle h1
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
    have h3 : ∑ k, Sum.elim (fun i => - c i) b k * Sum.elim x y k ∈ maximalIdeal R ^ 2 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, ← huv, neg_mul, Finset.sum_neg_distrib]
      simpa using hv
    intro j
    rw [← hb j, ← hmax]
    exact Ideal.mem_map_of_mem _ (hxy.indep _ h3 (Sum.inr j))
  have hs := card_le_dim _ s _ hy
  refine le_antisymm hJ fun t ht => ?_
  by_contra hn
  have : IsDomain (R ⧸ Ideal.span (Set.range x)) := (Ideal.Quotient.isDomain_iff_prime _).2 hp
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range x)) t ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h4 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hJ)
    (Ideal.Quotient.factor_surjective hJ) (mem_nonZeroDivisors_of_ne_zero h0)
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ht)
  have h5 : ((s : WithBot ℕ∞) + 1) + (Fintype.card (Fin r) : ℕ) ≤ ringKrullDim R := by
    rw [← hd]
    gcongr
    exact le_trans (by gcongr) h4
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc] at h5
  have h6 : s + 1 + Fintype.card (Fin r) ≤ Fintype.card (Fin r) + s := by exact_mod_cast h5
  omega
