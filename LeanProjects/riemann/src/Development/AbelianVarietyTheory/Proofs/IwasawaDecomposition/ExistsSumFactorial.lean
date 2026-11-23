import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogKer

theorem exists_sum_factorial {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : 0 < l)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A) (γ : ℕ → R) :
    ∃ Y : A, ∀ r n : ℕ, l ^ r ≤ n → ∃ w : A,
      Y = f (∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : R) * γ k) + (l : A) ^ r * w := by
  obtain ⟨Y, hY⟩ := LogEx.exists_sum (l : A) (fun k => f ((-1) ^ k * ((k.factorial : ℕ) : R) * γ k))
    (fun r => l ^ r) (fun a b hab => Nat.pow_le_pow_right hl hab) (fun r k hk => by
      obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hl r) hk
      refine ⟨f ((-1) ^ k * (m : R) * γ k), ?_⟩
      simp only [hm, map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]
      ring)
  refine ⟨Y, fun r n hn => ?_⟩
  obtain ⟨w, hw⟩ := hY r n hn
  exact ⟨w, by rw [map_sum, ← hw]; ring⟩

theorem sum_eq {P : Type} [CommRing P] (u γ : ℕ → P) (x : P) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : P) * u k = 1)
    (hγ : ∀ k : ℕ, (((k + 1).factorial : ℕ) : P) * γ k = x ^ (k + 1)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : P) * γ k =
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hγ k, Nat.factorial_succ, Nat.cast_mul]
  linear_combination (-((-1) ^ k * ((k.factorial : ℕ) : P) * γ k)) * hu k

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_log : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ z : Per.Ainf l, Per.θ l z = 0 → ∃ Y : Per.Acris l, ∀ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n (j Y) = Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) := by
  intro l _ j hj z hz
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  have hγ : ∀ k : ℕ, ∃ γ : Per.Acris0 l, (((k + 1).factorial : ℕ) : Per.AinfP l) * (γ : Per.AinfP l) =
      (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := fun k => by
    obtain ⟨d, hd⟩ := (hf (k + 1)).exists_right_inv
    have h : (((k + 1).factorial : ℕ) : Per.AinfP l) *
        (d * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) =
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l z (k + 1) _ hz h⟩, h⟩
  choose γ hγ using hγ
  have hmem : algebraMap (Per.Ainf l) (Per.AinfP l) z ∈ Per.kerP l :=
    GlobalTheory.RingIface.alg_mem_kerP l hz
  obtain ⟨Y, hY⟩ := exists_sum_factorial (algebraMap (Per.Acris0 l) (Per.Acris l)) l
    (Fact.out : l.Prime).pos (acris_basic l).1 γ
  refine ⟨Y, fun n => ?_⟩
  have hs : ∀ m : ℕ, ((∑ k ∈ Finset.range m, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * γ k :
      Per.Acris0 l) : Per.AinfP l) =
      ∑ k ∈ Finset.range m, (-1) ^ k * u k * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by
    intro m
    rw [← sum_eq u (fun k => (γ k : Per.AinfP l)) _ hu hγ m]
    change (Per.Acris0 l).val _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_natCast, map_neg, map_one]
    rfl
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n Y (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨w, hw⟩ := hY r (max (l ^ r) n) (le_max_left _ _)
    refine ⟨_, w, 0, hw, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ hmem (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

end GlobalTheory.MemLoc.LogKer
