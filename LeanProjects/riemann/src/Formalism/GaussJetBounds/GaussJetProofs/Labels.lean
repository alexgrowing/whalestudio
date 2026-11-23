import Formalism.GaussJetBounds.FrameJetEval
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem bddAbove_norm_coeff {R : Type} [NormedField R] {σ : Type} (Q : MvPolynomial σ R) :
    BddAbove (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖) := by
  classical
  have hfin : (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖).Finite := by
    refine Set.Finite.subset
      ((Q.support.image fun n => ‖MvPolynomial.coeff n Q‖).finite_toSet.insert 0) ?_
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ Q.support
    · right
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn)
    · left
      simp only [MvPolynomial.notMem_support_iff.1 hn, norm_zero]
  exact hfin.bddAbove

theorem gauss_sum_powers : GaussPow := by
  classical
  intro F K _ _ φ σ Y h k hk Q n
  let E : (σ →₀ ℕ) → (σ →₀ ℕ) := fun n =>
    Finsupp.onFinset n.support (fun y => k y * n y) (fun y hy => by
      rw [Finsupp.mem_support_iff]
      exact fun h0 => hy (by rw [h0, Nat.mul_zero]))
  have hEa : ∀ n y, E n y = k y * n y := fun n y => rfl
  have hE : Function.Injective E := by
    intro n n' hnn
    ext y
    have := congrArg (fun f => f y) hnn
    simp only [hEa] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hk y)) this
  let Q' : MvPolynomial σ F := ∑ n ∈ Q.support, MvPolynomial.monomial (E n) (MvPolynomial.coeff n Q)
  have h1 : MvPolynomial.eval₂ φ Y Q' = MvPolynomial.eval₂ φ (fun y => Y y ^ k y) Q := by
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.eval₂_monomial, Finsupp.onFinset_prod _ (fun _ => pow_zero _)]
    congr 1
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [pow_mul]
  have hc : ∀ n, MvPolynomial.coeff (E n) Q' = MvPolynomial.coeff n Q := by
    intro n
    simp only [Q', MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hE.eq_iff]
    rw [Finset.sum_ite_eq' Q.support n]
    split_ifs with hn
    · rfl
    · exact (MvPolynomial.notMem_support_iff.1 hn).symm
  rw [← h1, h, ← hc]
  exact le_ciSup (bddAbove_norm_coeff Q') (E n)

theorem labelsExist_statement : LabelsExist := by
  classical
  intro l d N0 _ hl TT nu1 size a ha hnu hsize hN
  let S : ZMod d → Finset ℤ := fun s =>
    (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ s - (j : ZMod d) ∈ TT ∧
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) ∧ (j < 0 → l ^ (-j).toNat ≤ size s))

  have hpow : ∀ (s : ZMod d) (j : ℤ), Odd j →
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) → (j < 0 → l ^ (-j).toNat ≤ size s) →
      l ^ j.natAbs ≤ a := by
    intro s j hj h1 h2
    rcases lt_trichotomy j 0 with h | h | h
    · have : (-j).toNat = j.natAbs := by omega
      rw [← this]
      exact (h2 h).trans (hsize s)
    · subst h
      exact absurd hj (by decide)
    · have : j.toNat = j.natAbs := by omega
      rw [← this]
      exact (h1 h).trans (hnu _)
  have hIcc : ∀ j : ℤ, l ^ j.natAbs ≤ a → j ∈ Finset.Icc (-(a : ℤ)) a := by
    intro j hj
    have h1 : j.natAbs < l ^ j.natAbs := Nat.lt_pow_self hl
    rw [Finset.mem_Icc]
    omega
  have hcard : ∀ s, ((S s).card : ℝ) ≤ 2 * Real.logb l a + 1 := by
    intro s
    refine le_trans ?_ (oddExponentCount l a hl ha)
    exact_mod_cast Finset.card_le_card (by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hj.2.1, hpow s j hj.2.1 hj.2.2.2.1 hj.2.2.2.2⟩)
  refine ⟨fun s => (S s).card,
    fun s i => (s - ((((S s).equivFin.symm i : S s) : ℤ) : ZMod d), (((S s).equivFin.symm i : S s) : ℤ)),
    a, ?_, ?_, ?_, ?_⟩
  · intro s i i' hii
    have h2 := congrArg Prod.snd hii
    simp only at h2
    exact (S s).equivFin.symm.injective (Subtype.ext h2)
  · intro s s0 j
    constructor
    · rintro ⟨i, hi⟩
      have hm := ((S s).equivFin.symm i).2
      have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      simp only at h1 h2
      rw [h2] at h1 hm
      simp only [S, Finset.mem_filter] at hm
      rw [h1] at hm
      exact ⟨hm.2.2.1, hm.2.1, by rw [← h1]; ring, hm.2.2.2.1, hm.2.2.2.2⟩
    · rintro ⟨hT, hodd, hs, hp, hn⟩
      have hs0 : s - (j : ZMod d) = s0 := by rw [hs]; ring
      have hm : j ∈ S s := by
        simp only [S, Finset.mem_filter]
        rw [hs0]
        exact ⟨hIcc j (hpow s j hodd (by rw [hs0]; exact hp) hn), hodd, hT, hp, hn⟩
      refine ⟨(S s).equivFin ⟨j, hm⟩, ?_⟩
      simp only [Equiv.symm_apply_apply, hs0]
  · intro s
    have h1 := hcard s
    have h2 : ((S s).card : ℝ) + 1 ≤ (N0 : ℝ) := by linarith
    have h3 : (S s).card + 1 ≤ N0 := by exact_mod_cast h2
    show (S s).card + _ ≤ N0
    split_ifs <;> omega
  · intro s i
    show (-(((S s).equivFin.symm i : S s) : ℤ)).toNat ≤ a
    obtain ⟨j, hm⟩ := (S s).equivFin.symm i
    have hm' := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
    show (-j).toNat ≤ a
    omega

end Formalism.DworkPowerSeriesWeights
