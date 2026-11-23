import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZeroStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.MovedIdx

theorem common_denom {A ι : Type} [CommRing A] [Fintype ι] (S : Subring A) (f : ι → A) (P : ℕ → Prop) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (h : ∀ i, ∃ n : ℕ, P n ∧ (n : A) * f i ∈ S) :
    ∃ n : ℕ, P n ∧ ∀ i, (n : A) * f i ∈ S := by
  choose n hn hf using h
  refine ⟨∏ i, n i, Finset.prod_induction _ P hm h1 fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_comm (n i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem S c) (hf i)

theorem dvd_of_dvd_idx {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (A B : Submodule R X) (n q : ℕ)
    (hq : q.Prime) (h0 : idx A B ≠ 0) (hn : ∀ x ∈ B, n • x ∈ A) (hd : q ∣ idx A B) : q ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) q hd
  rw [← hx, addOrderOf_dvd_iff_nsmul_eq_zero]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hn y.1 y.2

theorem denom_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ∃ n : ℕ, n.Coprime q ∧ (n : AE D) * (y * x) ∈ OhE D := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, -, hmq, s, hs, h⟩ := hx a
  refine ⟨m * n', Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, ?_⟩
  convert mul_mem hs hy using 1
  push_cast
  linear_combination (n' : AE D) * y * h

theorem one_entry_mem (D : D7) {N : ℕ} (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem denom_triv (D : D7) {q N : ℕ} {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2)
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (by
      rintro ⟨i, j⟩
      obtain ⟨m, -, hm, s, hs, e⟩ := hg i j 0
      refine ⟨m, hm, ?_⟩
      convert add_mem hs (mul_mem (natCast_mem _ m) (one_entry_mem D i j)) using 1
      linear_combination e)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem denom_triv_inv (D : D7) {q N : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N × Fin N =>
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2.1 *
      ((g : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2))
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (fun p => denom_mul D hq (hg _ _) _)
  refine ⟨n, hn, fun i j => ?_⟩
  have e : ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      1 - ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * ((g : Matrix (Fin N) (Fin N) (AE D)) - 1) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, sub_sub_cancel]
  rw [e, Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum]
  exact sub_mem (mul_mem (natCast_mem _ n) (one_entry_mem D i j)) (sum_mem fun l _ => h (i, l, j))

theorem denom_mat (D : D7) {N : ℕ} (M : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * M i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => M p.1 p.2)
    (fun n => 0 < n) one_pos (fun a b => Nat.mul_pos) (fun p => GlobalTheory.HeckeVal.exists_denom D _)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem nsmul_mem_latA (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (g : GA D N) (g' : GA D N') {n n' : ℕ}
    (h : ∀ i j, (n : AE D) * (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (h' : ∀ i j, (n' : AE D) * ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D) :
    ∀ ζ ∈ (latA D cc N N').map (actA D N N' (g, g')), (n * n') • ζ ∈ latA D cc N N' := by
  rintro _ ⟨ζ, hζ, rfl⟩ i j
  rw [actA_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  convert ihE_mul D cc (mul_mem (h l j) (h' i k)) (hζ k l) using 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.FinWeil.MovedIdx

open GlobalTheory.FinWeil.MovedIdx in

theorem GlobalTheory.FinWeil.idx_map_actA : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  intro D hD cc δ hC N N' g g'
  have h0 : idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 := by
    obtain ⟨n, hn, h⟩ := denom_mat D (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    obtain ⟨n', hn', h'⟩ := denom_mat D ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    exact GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hD cc δ hC N N' _ (Nat.mul_pos hn hn') _ (nsmul_mem_latA D cc g g' h h')
  refine ⟨h0, fun q hq hg hg' hd => ?_, fun hg hg' ζ hζ => ?_⟩
  · obtain ⟨n, hn, h⟩ := denom_triv_inv D hq hg
    obtain ⟨n', hn', h'⟩ := denom_triv D hg'
    exact (Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.mul_left hn hn').symm
      (dvd_of_dvd_idx _ _ _ q hq h0 (nsmul_mem_latA D cc g g' h h') hd)
  · have := nsmul_mem_latA D cc g g' (n := 1) (n' := 1) (fun i j => by simpa using (hg i j).2)
      (fun i j => by simpa using (hg' i j).1) ζ hζ
    simpa using this
