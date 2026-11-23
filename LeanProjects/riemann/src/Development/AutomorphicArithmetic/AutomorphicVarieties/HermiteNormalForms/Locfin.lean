import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.locfin :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N → ∀ B : ℝ,
    ∃ S : Set (Lat L N), S.Finite ∧ ∀ᶠ k in nhds h, ∀ y ∉ S, B < q k y := by
  intro L _ _ N h hh B
  obtain ⟨c, hc, hev⟩ := lowbd L N h hh
  obtain ⟨R, hR⟩ := exists_nat_gt (max (B / c) 1)
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRB : B / c < R := lt_of_le_of_lt (le_max_left _ _) hR
  set T := {a : 𝓞 L | ∀ w : InfinitePlace L, ‖embO w a‖ ≤ (R : ℝ)} with hT
  refine ⟨Set.pi Set.univ (fun _ => T), Set.Finite.pi (fun _ => (cntconj L R).1), ?_⟩
  filter_upwards [hev] with k hk
  intro y hy
  have hy' : ∃ a w, (R : ℝ) < ‖embO w (y a)‖ := by
    by_contra hne
    push_neg at hne
    exact hy (fun a _ w => hne a w)
  obtain ⟨a, w, hlt⟩ := hy'
  have hle : ‖embO w (y a)‖ ≤ ‖toR y‖ :=
    (norm_le_pi_norm (toR y w) a).trans (norm_le_pi_norm (toR y) w)
  have hzR : (R : ℝ) < ‖toR y‖ := hlt.trans_le hle
  have hz1 : (1 : ℝ) ≤ ‖toR y‖ := hR1.le.trans hzR.le
  have hsq : ‖toR y‖ ≤ ‖toR y‖ ^ 2 := by nlinarith
  have hB : B < c * ‖toR y‖ := by
    rw [div_lt_iff₀ hc] at hRB
    nlinarith
  exact lt_of_lt_of_le (hB.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)) (hk (toR y))
