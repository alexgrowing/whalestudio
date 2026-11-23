import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfFree

namespace PositivityTheory.KCo

theorem good_split_of_cm : GoodSplit := by
  intro F E _ _ _ _ _ σ B hB v hs
  have hcm := hB.cm
  haveI hgal : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  set p : Ideal ℤ := Ideal.under ℤ v.asIdeal with hp
  have hs' : (p.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank ℚ E := hs
  have hfin : (p.primesOver (NumberField.RingOfIntegers E)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hs']; exact Module.finrank_pos.ne')
  haveI : Fintype (p.primesOver (NumberField.RingOfIntegers E)) := hfin.fintype
  have hA : ∀ q ∈ p.primesOver (NumberField.RingOfIntegers E),
      q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1 := by
    have hsum := Ideal.sum_ramification_inertia_eq_finrank p (NumberField.RingOfIntegers E)
    rw [NumberField.RingOfIntegers.rank] at hsum
    have hcard : Fintype.card (p.primesOver (NumberField.RingOfIntegers E)) = Module.finrank ℚ E := by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hs']
    have hpos : ∀ x : p.primesOver (NumberField.RingOfIntegers E),
        1 ≤ x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ := by
      intro x
      haveI : x.1.IsPrime := x.2.1
      exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
    intro q hq
    by_contra hne
    have hlt : ∑ _x : p.primesOver (NumberField.RingOfIntegers E), (1 : ℕ) <
        ∑ x : p.primesOver (NumberField.RingOfIntegers E), x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ :=
      Finset.sum_lt_sum (fun x _ => hpos x)
        ⟨⟨q, hq⟩, Finset.mem_univ _, lt_of_le_of_ne (hpos ⟨q, hq⟩) (Ne.symm hne)⟩
    rw [hsum] at hlt
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hlt
    exact lt_irrefl _ hlt
  have hB1 : ∀ Q ∈ v.asIdeal.primesOver (NumberField.RingOfIntegers E),
      Q.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        Q.inertiaDeg (NumberField.RingOfIntegers F) = 1 := by
    intro Q hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver v.asIdeal := hQ.2
    haveI : v.asIdeal.LiesOver p := ⟨rfl⟩
    haveI : Q.LiesOver p := Ideal.LiesOver.trans Q v.asIdeal p
    have h1 := hA Q ⟨inferInstance, inferInstance⟩
    rw [Ideal.ramificationIdx_tower (R := ℤ) (q := v.asIdeal) (r := Q),
      Ideal.inertiaDeg_tower (R := ℤ) (q := v.asIdeal) (r := Q)] at h1
    have h2 := mul_eq_one.mp h1
    exact ⟨(mul_eq_one.mp h2.1).2, (mul_eq_one.mp h2.2).2⟩
  have hC := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal
    (NumberField.RingOfIntegers E) (E ≃ₐ[F] E)
  have hG : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact hcm.2.2.1
  rw [hG] at hC
  have hne : (v.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hC
    exact absurd hC (by norm_num)
  obtain ⟨Q, hQ⟩ := Set.nonempty_of_ncard_ne_zero hne
  haveI : Q.IsPrime := hQ.1
  haveI : Q.LiesOver v.asIdeal := hQ.2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q (E ≃ₐ[F] E), (hB1 Q hQ).1, (hB1 Q hQ).2,
    mul_one, mul_one] at hC
  exact (GlobalTheory.AdelicU.nonempty_split_iff hcm).mpr hC

end PositivityTheory.KCo
