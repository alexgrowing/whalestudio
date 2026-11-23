import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogFun

theorem partial_eq {R : Type} [CommRing R] (u : ℕ → R) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : R) * u k = 1)
    (x s : R) (n : ℕ) (hn : IsUnit ((n.factorial : ℕ) : R))
    (hs : ((n.factorial : ℕ) : R) * s =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * x ^ (k + 1)) :
    s = ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  apply hn.mul_left_cancel
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : R) = ((n.factorial / (k + 1) : ℕ) : R) * ((k + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, ← h1]
  generalize ((n.factorial / (k + 1) : ℕ) : R) = q at h2 ⊢
  rw [h2]
  linear_combination (-((-1) ^ k * q * x ^ (k + 1))) * hu k

theorem partial_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u : ℕ → R) (x : R) (hx : x ∈ I)
    {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.range m, (-1) ^ k * u k * x ^ (k + 1) -
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) ∈ I ^ n := by
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.1 hk).1; omega) (Ideal.pow_mem_pow hx (k + 1))

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem {e : Per.Fl l} (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ∈ Per.kerP l := by
  exact GlobalTheory.RingIface.alg_mem_kerP l (by rw [Model.theta_mu, he, sub_self])

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem isLog_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) : Per.IsLog l e (j t) := by
  refine GlobalTheory.CrisIncl.isLog_of_partial l e he _ fun n => ?_
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      partial_eq u hu _ _ _ (hf _) hs, partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (partial_sub_mem _ u _ (mu_mem he) (le_max_right _ _)))
  exact ⟨c, hc, by rw [key, ev_alg]⟩

theorem log_fun : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) :=
  fun _ _ _ _ he ht => ⟨fun _ h => Model.isLogA_unique h ht, fun g => Model.isLogA_sigA g ht,
    Model.isLogA_phiA ht, fun _ hj => isLog_map he ht hj⟩

end GlobalTheory.MemLoc.LogFun
