import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.SmallFirst

theorem coeff_single_frob {Q : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {d : ℕ}
    (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    coeff (Finsupp.single i p) (frob p s f) = s (lin f i) := by
  have h1 : frob p s f = expand p hp (map s f) := by
    rw [frob, expand, substAlgHom_apply]
  have h2 : (Finsupp.single i p : Fin d →₀ ℕ) = p • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, h2, coeff_expand_smul, coeff_map, lin]

theorem coeff_comb {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ l, algebraMap B Q (b l) * coeff α (e l) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MvPowerSeries.coeff_smul]

end GlobalTheory.QLog.SmallFirst

theorem GlobalTheory.QLog.small_first_of_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU w hw i
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set J : Ideal F.B := Ideal.comap F.θ (IsLocalRing.maximalIdeal O) with hJ
  have memJ : ∀ x, x ∈ J ↔ ¬IsUnit (F.θ x) := fun x => by
    rw [hJ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpJ : (p : F.B) ∈ J := by
    rw [memJ, map_natCast]; exact Fact.out
  haveI hJp : J.IsPrime := Ideal.IsPrime.comap F.θ
  set α : Fin d →₀ ℕ := Finsupp.single i p with hα

  have hc : ∀ l, ∃ cl : F.B, (p : F.Q) * coeff α (e l) = algebraMap F.B F.Q cl := by
    intro l
    obtain ⟨b, -, hb⟩ := GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hlift ⊤ (e l) (hbas.1 l) α i
    refine ⟨b, ?_⟩
    rw [← hb, hα, Finsupp.single_eq_same]
  choose cc hcc using hc
  have key : ∀ m, algebraMap F.B F.Q (∑ l, U l m * cc l) =
      (p : F.Q) * ∑ l, algebraMap F.B F.Q (U l m) * coeff α (e l) := by
    intro m
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← hcc]; ring
  have hcol : ∀ m l, (U * blk d k (p : F.B) 1) l m = U l m * Sum.elim (fun _ => (p : F.B)) (fun _ => 1) m := by
    intro m l
    rw [blk, Matrix.mul_diagonal]
  have hR : ∀ m, (∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0) ∈ J := by
    intro m
    cases m with
    | inl i' =>
      obtain ⟨t, ht, hteq⟩ := (hU (Sum.inl i')).2 i' rfl α
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, (hadp i').2, SmallFirst.coeff_comb] at hteq
      have hs : F.s (Pi.single (M := fun _ : Fin d => F.Q) i' 1 i) =
          algebraMap F.B F.Q (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0) := by
        by_cases h : i' = i
        · subst h; simp
        · have h' : i ≠ i' := Ne.symm h
          simp [Pi.single_apply, h', h]
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inl i')) * coeff α (e l) =
          algebraMap F.B F.Q (∑ l, U l (Sum.inl i') * cc l) := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inl, map_mul, map_natCast]; ring
      rw [hs, hsum, ← map_sub] at hteq
      have := F.frame.inj hteq
      have h2 : (∑ l, U l (Sum.inl i') * cc l) - (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0)
          = -(t' * p) := by rw [← this]; ring
      rw [h2]
      exact J.neg_mem (J.mul_mem_left _ hpJ)
    | inr j =>
      obtain ⟨b, -, hb⟩ := (hbas.1 (Sum.inr j)).2.1 i
      obtain ⟨t, -, hteq⟩ := (hU (Sum.inr j)).1 α
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, hb, F.s_alg, SmallFirst.coeff_comb] at hteq
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inr j)) * coeff α (e l) =
          ∑ l, algebraMap F.B F.Q (U l (Sum.inr j)) * coeff α (e l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inr, mul_one]
      rw [hsum] at hteq
      have h3 : algebraMap F.B F.Q (∑ l, U l (Sum.inr j) * cc l) =
          algebraMap F.B F.Q ((p : F.B) * (F.σ b - t)) := by
        rw [key, map_mul, map_sub, map_natCast, ← hteq]; ring
      have h4 := F.frame.inj h3
      have hne : (Sum.inr j : Fin d ⊕ Fin k) ≠ Sum.inl i := Sum.inr_ne_inl
      rw [if_neg hne, sub_zero, h4]
      exact J.mul_mem_right _ hpJ

  have hW : ∑ m, F.σ (w m) * ∑ l, U l m * cc l ∈ J := by
    have : ∑ m, F.σ (w m) * ∑ l, U l m * cc l = ∑ l, U.mulVec (fun j => F.σ (w j)) l * cc l := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    exact J.sum_mem fun l _ => J.mul_mem_right _ ((memJ _).2 (hw l))
  have hD : ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) ∈ J :=
    J.sum_mem fun m _ => J.mul_mem_left _ (hR m)
  have hσ : F.σ (w (Sum.inl i)) ∈ J := by
    have : F.σ (w (Sum.inl i)) = (∑ m, F.σ (w m) * ∑ l, U l m * cc l) -
        ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [this]
    exact J.sub_mem hW hD
  obtain ⟨z, hz⟩ := F.σ_pow (w (Sum.inl i))
  have hpow : w (Sum.inl i) ^ p ∈ J := by
    have : w (Sum.inl i) ^ p = F.σ (w (Sum.inl i)) - p * z := by rw [← hz]; ring
    rw [this]
    exact J.sub_mem hσ (J.mul_mem_right _ hpJ)
  exact (memJ _).1 (hJp.mem_of_pow_mem p hpow)
