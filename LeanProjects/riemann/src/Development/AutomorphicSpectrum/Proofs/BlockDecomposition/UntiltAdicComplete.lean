import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem exists_lim_of_dvd {R : Type*} [CommRing R] (p : R) [IsAdicComplete (Ideal.span {p}) R]
    (g : ℕ → R) (hg : ∀ n, p ^ n ∣ g (n + 1) - g n) : ∃ y, ∀ n, p ^ n ∣ g n - y := by
  have chain : ∀ m k, p ^ m ∣ g (m + k) - g m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ m ∣ g (m + k + 1) - g (m + k) :=
        (pow_dvd_pow p (Nat.le_add_right m k)).trans (hg (m + k))
      have := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) g (fun {m n} hmn => by
    rw [smodEq_span_singleton_pow_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (dvd_sub_comm).1 (chain m k))
  exact ⟨L, fun n => (smodEq_span_singleton_pow_iff _ _ _ _).1 (hL n)⟩

theorem isAdicComplete_quotient {R : Type*} [CommRing R] (p ξ : R)
    [IsAdicComplete (Ideal.span {p}) R] (h : ∀ (n : ℕ) (x : R), p ^ n ∣ ξ * x → p ^ n ∣ x) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
  have hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ∀ n : ℕ, ∃ y z, a = ξ * y + p ^ n * z := by
      intro n
      have hd := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hx n)
      rw [sub_zero] at hd
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h0 : Ideal.Quotient.mk (Ideal.span {ξ}) (a - p ^ n * c') = 0 := by
        rw [map_sub, map_mul, map_pow, hc, sub_self]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact ⟨y, c', by linear_combination hy⟩
    choose y z hyz using h1
    have hy : ∀ n, p ^ n ∣ y (n + 1) - y n := fun n =>
      h n _ ⟨z n - p * z (n + 1), by linear_combination hyz n - hyz (n + 1)⟩
    obtain ⟨Y, hY⟩ := exists_lim_of_dvd p y hy
    have hz : a - ξ * Y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {p}) _ fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero]
      obtain ⟨c, hc⟩ := hY n
      exact ⟨ξ * c + z n, by linear_combination hyz n + ξ * hc⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨Y, sub_eq_zero.1 hz⟩)
  have hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun f hf => ?_⟩
    have step : ∀ (n : ℕ) (x : R), Ideal.Quotient.mk (Ideal.span {ξ}) x = f n →
        ∃ y, Ideal.Quotient.mk (Ideal.span {ξ}) y = f (n + 1) ∧ p ^ n ∣ y - x := by
      intro n x hx
      obtain ⟨c, hc⟩ := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hf (Nat.le_succ n))
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨x - p ^ n * c', ?_, ⟨-c', by ring⟩⟩
      rw [map_sub, map_mul, map_pow, hx, ← hc]
      ring
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (f 0)
    let G : ∀ n, {x : R // Ideal.Quotient.mk (Ideal.span {ξ}) x = f n} := fun n =>
      Nat.rec ⟨x0, hx0⟩ (fun n x => ⟨(step n x.1 x.2).choose, (step n x.1 x.2).choose_spec.1⟩) n
    have hG : ∀ n, p ^ n ∣ (G (n + 1)).1 - (G n).1 := fun n => (step n _ (G n).2).choose_spec.2
    obtain ⟨y, hy⟩ := exists_lim_of_dvd p (fun n => (G n).1) hG
    refine ⟨Ideal.Quotient.mk _ y, fun n => ?_⟩
    rw [smodEq_span_singleton_pow_iff]
    have := map_dvd (Ideal.Quotient.mk (Ideal.span {ξ})) (hy n)
    rwa [map_pow, map_sub, (G n).2] at this
  exact { hH, hP with }

theorem isAdicComplete_U : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  intro l _ A
  have hc := isAdicComplete_quotient (l : A.W) A.xi (fun n x hx =>
    Ideal.mem_span_singleton.1 ((GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.2 n x (Ideal.mem_span_singleton.2 hx)))
  have e : (l : A.U) = Ideal.Quotient.mk (Ideal.span {A.xi}) (l : A.W) := (map_natCast A.th l).symm
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.Untilt
