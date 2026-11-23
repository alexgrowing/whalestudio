import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial Cardinal

noncomputable section

namespace FreeParAlgIndep

theorem genPar_algIndep (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem algebraicIndependent_of_trdeg {k L : Type} [Field k] [Field L] [Algebra k L]
    (A₀ : Subalgebra k L) {ι : Type} [Finite ι] (w : ι → L)
    [Algebra.IsAlgebraic (Algebra.adjoin A₀ (Set.range w)) L] {e : ℕ}
    (htr : Algebra.trdeg k A₀ ≤ e) (hle : (e : Cardinal) + #ι ≤ Algebra.trdeg k L) :
    AlgebraicIndependent A₀ w := by
  have : FaithfulSMul k A₀ :=
    (faithfulSMul_iff_algebraMap_injective k A₀).2 (algebraMap k A₀).injective
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective A₀ L).2 Subtype.val_injective
  have hadd := trdeg_add_eq k A₀ (A := L)
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite A₀ w ?_).1
  have h3 : #ι + (e : Cardinal) ≤ Algebra.trdeg A₀ L + e := by
    rw [add_comm, add_comm _ (e : Cardinal)]
    refine hle.trans ?_
    rw [← hadd]
    gcongr
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).1 h3

theorem proof : FreeParAlgIndep.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hgen hU hT j₀ hx0 htr
  generalize hz : (fun m => x m * (x j₀)⁻¹) = z at htr ⊢
  have hzm : ∀ m, z m = x m * (x j₀)⁻¹ := fun m => by rw [← hz]
  have hz0 : z j₀ = 1 := by rw [hzm, mul_inv_cancel₀ hx0]
  rw [IntermediateField.algebraicIndependent_adjoin_iff]

  let w : (Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n → L :=
    Sum.elim (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1))))
      (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inr j)))
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin (Algebra.adjoin k (Set.range z)) (Set.range w)) L := by
    set A₀ := Algebra.adjoin k (Set.range z) with hA₀
    set B := Algebra.adjoin A₀ (Set.range w) with hB
    have hzB : ∀ m, z m ∈ B := fun m =>
      Subalgebra.algebraMap_mem B (⟨z m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : A₀)
    have hwB : ∀ i, w i ∈ B := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
    have hkB : ∀ c : k, algebraMap k L c ∈ B := fun c => by
      rw [IsScalarTower.algebraMap_apply k A₀ L]
      exact Subalgebra.algebraMap_mem B _
    have hparB : ∀ p, algebraMap (GenParField k e n) L (genPar k e n p) ∈ B := by
      rintro (⟨i, j⟩ | j)
      · by_cases hj : j = j₀
        · rw [hj]
          have hsum : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
            simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
          have h1 := Finset.add_sum_erase Finset.univ
            (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j)
            (Finset.mem_univ j₀)
          simp only [hz0, mul_one] at h1
          rw [hsum, ← eq_neg_iff_add_eq_zero] at h1
          rw [h1]
          refine neg_mem (Subalgebra.sum_mem _ fun j' hj' => Subalgebra.mul_mem _ ?_ (hzB j'))
          exact hwB (.inl (i, ⟨j', Finset.ne_of_mem_erase hj'⟩))
        · exact hwB (.inl (i, ⟨j, hj⟩))
      · exact hwB (.inr j)
    have hmem : ∀ b ∈ B, IsAlgebraic B b := fun b hb => isAlgebraic_algebraMap (⟨b, hb⟩ : B)
    have hx0alg : IsAlgebraic B (x j₀) := by
      have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
        simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
      have h2 : IsAlgebraic B
          (∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j) :=
        hmem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hwB (.inr j)) (hzB j))
      have := h2.inv
      rwa [hs, inv_inv] at this
    have hxalg : ∀ m, IsAlgebraic B (x m) := fun m => by
      have hm : x m = z m * x j₀ := by rw [hzm, inv_mul_cancel_right₀ hx0]
      rw [hm]
      exact (hmem _ (hzB m)).mul hx0alg
    have hpoly : ∀ a : MvPolynomial (Par e n) k, algebraMap (GenParField k e n) L
        (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) a) ∈ B := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C c =>
        rw [← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n),
          ← IsScalarTower.algebraMap_apply k (GenParField k e n) L]
        exact hkB c
      | add a b ha hb =>
        rw [map_add, map_add]
        exact Subalgebra.add_mem _ ha hb
      | mul_X a p ha =>
        rw [map_mul, map_mul]
        exact Subalgebra.mul_mem _ ha (hparB p)
    have hK : ∀ f, IsAlgebraic B (algebraMap (GenParField k e n) L f) := fun f => by
      obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Par e n) k) f
      rw [map_div₀, div_eq_mul_inv]
      exact (hmem _ (hpoly a)).mul (hmem _ (hpoly b)).inv
    refine ⟨fun y => ?_⟩
    have hy : y ∈ (MvPolynomial.aeval (R := GenParField k e n) x).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]
      trivial
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
    clear hy
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C]
      exact hK c
    | add a b ha hb =>
      rw [map_add]
      exact ha.add hb
    | mul_X a j ha =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact ha.mul (hxalg j)

  have hcard : (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n) ≤
      Algebra.trdeg k L := by
    have hind : AlgebraicIndependent k
        (fun p => algebraMap (GenParField k e n) L (genPar k e n p)) :=
      (genPar_algIndep k e n).map' (f := IsScalarTower.toAlgHom k (GenParField k e n) L)
        (algebraMap (GenParField k e n) L).injective
    have hinj : Function.Injective (Sum.elim (fun i : Fin e => (Sum.inl (i, j₀) : Par e n))
        (Sum.elim (fun p : Fin e × {j : Fin n // j ≠ j₀} => (Sum.inl (p.1, p.2.1) : Par e n))
          Sum.inr)) := by
      rintro (i | ⟨i, j, hj⟩ | j) (i' | ⟨i', j', hj'⟩ | j') h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
          reduceCtorEq, Subtype.mk.injEq, and_true] at h ⊢ <;>
        first | exact h | exact absurd h.2.symm hj' | exact absurd h.2 hj
    calc (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)
        = #(Fin e ⊕ ((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)) := by simp
      _ ≤ #(Par e n) := Cardinal.mk_le_of_injective hinj
      _ ≤ Algebra.trdeg k L := hind.cardinalMk_le_trdeg
  exact (algebraicIndependent_of_trdeg (Algebra.adjoin k (Set.range z)) w htr hcard).comp
    Sum.inl Sum.inl_injective

end FreeParAlgIndep

end

end GroundTheory.Heights₂.Heights.Vertical
