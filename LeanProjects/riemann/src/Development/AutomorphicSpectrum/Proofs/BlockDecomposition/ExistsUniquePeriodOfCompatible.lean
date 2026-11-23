import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem existsUnique_limit_of_dvd {R : Type*} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (z : ℕ → R)
    (hz : ∀ m, t ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃! x : R, ∀ m, t ^ (m + 1) ∣ x - z m := by
  have hmem : ∀ (n : ℕ) (a : R), a ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule R R) ↔ t ^ n ∣ a := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hchain : ∀ {m n : ℕ}, m ≤ n → t ^ m ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : t ^ m ∣ z (n + 1) - z n := (pow_dvd_pow t (by omega)).trans (hz n)
      have h2 := dvd_add h1 ih
      simpa using h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) z (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, hmem]
    exact hchain hmn)
  refine ⟨L, fun m => ?_, fun x hx => ?_⟩
  · have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
      have := hL (m + 1)
      rw [SModEq.comm, SModEq.sub_mem, hmem] at this
      exact this
    have h2 := dvd_add h1 (hz m)
    simpa using h2
  · have hLd : ∀ m, t ^ (m + 1) ∣ L - z m := by
      intro m
      have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
        have := hL (m + 1)
        rw [SModEq.comm, SModEq.sub_mem, hmem] at this
        exact this
      have h2 := dvd_add h1 (hz m)
      simpa using h2
    refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)
    rw [SModEq.zero, hmem]
    have h3 := dvd_sub (hx n) (hLd n)
    have h4 : t ^ (n + 1) ∣ x - L := by simpa using h3
    exact (pow_dvd_pow t (Nat.le_succ n)).trans h4

theorem isAdicComplete_span_tBdR (l : ℕ) [Fact l.Prime] :
    IsAdicComplete (Ideal.span {tBdR l}) (BdRp l) := by
  rw [← maximalIdeal_eq_span_tBdR]
  exact IsPerfectoidField.instIsAdicCompleteMaximalIdealBdR

theorem pInv_rangeRestrict (l : ℕ) [Fact l.Prime] (b : BdRp l) :
    pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b) = b :=
  RingEquiv.symm_apply_apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩) b

theorem pInv_injective (l : ℕ) [Fact l.Prime] : Function.Injective (pInv l) :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.injective

theorem existsUnique_bdRp_of_compatible (l : ℕ) [Fact l.Prime]
    (y : ∀ m : ℕ, Bk l (m + 1)) (hy : ∀ m, dk l (m + 1) (y (m + 1)) = y m) :
    ∃! x : BdRp l, ∀ m, pk l (m + 1) x = y m := by
  haveI := isAdicComplete_span_tBdR l
  choose z hz using fun m => Ideal.Quotient.mk_surjective (y m)
  have key : ∀ (m : ℕ) (x : BdRp l), pk l (m + 1) x = y m ↔ tBdR l ^ (m + 1) ∣ x - z m := by
    intro m x
    rw [← hz m, pk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hstep : ∀ m, tBdR l ^ (m + 1) ∣ z (m + 1) - z m := by
    intro m
    rw [← key m]
    have := hy m
    rw [← hz (m + 1)] at this
    exact this
  obtain ⟨x, hx, hu⟩ := existsUnique_limit_of_dvd (tBdR l) z hstep
  exact ⟨x, fun m => (key m x).2 (hx m), fun x' hx' => hu x' fun m => (key m x').1 (hx' m)⟩

theorem levSys_existsUnique {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    {M : ℕ} (h : LevHyp l K M) :
    ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) →
      ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  intro y hy
  obtain ⟨b, hb, hu⟩ := existsUnique_bdRp_of_compatible l y hy
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict b, fun m => ?_, fun x' hx' => ?_⟩
  · change pk l (m + 1) (pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b)) = y m
    rw [pInv_rangeRestrict]
    exact hb m
  · refine pInv_injective l ?_
    rw [pInv_rangeRestrict]
    exact hu _ hx'

end GlobalTheory.CompanionTheory.LatC
