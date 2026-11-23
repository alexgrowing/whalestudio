import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanStep

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

theorem altsum (n : ℕ) : ∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ) = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    rcases Nat.even_or_odd n with h | h
    · have h' : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr (h.add_odd (by decide))
      simp [h, h', h.neg_one_pow]
    · have h' : ¬ Even n := Nat.not_even_iff_odd.mpr h
      have h'' : Even (n + 1) := h.add_odd (by decide)
      simp [h', h'', h.neg_one_pow]

theorem spanFor_subsingleton (G : Type) [Group G] [Subsingleton G] : SpanFor G := by
  intro q c hc hd
  obtain ⟨v, hv⟩ : ∃ v, ∀ y, c y = v := ⟨c (fun _ => 1), fun y => congrArg c (Subsingleton.elim _ _)⟩
  rcases Nat.even_or_odd q with hq | hq
  · have h3 : ¬ Even (q + 1 + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    have hd1 := congrFun hd (fun _ => 1)
    simp only [dc, hv, Pi.zero_apply] at hd1
    rw [← Finset.sum_mul, altsum, if_neg h3, one_mul] at hd1
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => 0, fun _ _ _ => rfl, ?_⟩
    funext y
    simp [dc, hv, hd1]
  · have h2 : ¬ Even (q + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => v, fun _ _ _ => rfl, ?_⟩
    funext y
    simp only [dc, hv, Finset.univ_eq_empty, Finset.sum_empty, Pi.add_apply, Pi.zero_apply, zero_add]
    rw [← Finset.sum_mul, altsum, if_neg h2, one_mul]

theorem spanFor_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (hB : SpanFor B) : SpanFor A := by
  intro q c hc hd
  obtain ⟨k, a, α, f, hf, hcf⟩ := hB q (fun z => c (fun j => e.symm (z j)))
    (fun g _ y => by
      simp only [map_mul]
      exact hc _ trivial _)
    (by
      funext z
      have := congrFun hd (fun j => e.symm (z j))
      simpa [dc] using this)
  refine ⟨k, a, fun i j => (α i j).comp (MulEquiv.toAdditive e).toAddMonoidHom, fun y => f (fun j => e (y j)),
    fun g _ y => ?_, ?_⟩
  · simp only [map_mul]
    exact hf _ trivial _
  · funext y
    have := congrFun hcf (fun j => e (y j))
    simp only [MulEquiv.symm_apply_apply] at this
    rw [this]
    simp [Finset.sum_apply, cupH, dc]

def zdata (N : ℕ) : WData (Multiplicative (Fin N → ℤ)) (Multiplicative (Fin (N + 1) → ℤ)) where
  ι := { toFun := fun g => Multiplicative.ofAdd (Fin.cons 0 (Multiplicative.toAdd g))
         map_one' := by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp
         map_mul' := fun g h => by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  ρ := { toFun := fun p => Multiplicative.ofAdd (Fin.tail (Multiplicative.toAdd p))
         map_one' := rfl
         map_mul' := fun _ _ => rfl }
  ℓ := { toFun := fun x => (Multiplicative.toAdd (Additive.toMul x)) 0
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
  t := Multiplicative.ofAdd (Fin.cons 1 0)
  ρι := fun _ => rfl
  ρt := rfl
  ℓι := fun g => by simp
  ℓt := by simp
  tc := fun z => mul_comm _ _
  dec := fun p => by
    apply Multiplicative.toAdd.injective; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
      try rfl

theorem spanFor_pi : ∀ N : ℕ, SpanFor (Multiplicative (Fin N → ℤ))
  | 0 => spanFor_subsingleton _
  | N + 1 => (zdata N).step' (spanFor_pi N)

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismSpan

theorem span : Span := by
  intro A _ _ _ q c hc hd
  let e : Multiplicative (Additive A) ≃* Multiplicative (Fin (Module.finrank ℤ (Additive A)) → ℤ) :=
    AddEquiv.toMultiplicative (Module.finBasis ℤ (Additive A)).equivFun.toAddEquiv
  exact spanFor_equiv e (spanFor_pi _) q c hc hd

end PositivityTheory.KB.SplitAffineSpectral

end
