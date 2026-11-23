import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EzOfComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GaussSumBound
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem GlobalTheory.HilbertThetaSeries.th_expansion : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  intro F _ _ _ κ _ _ G hG a Φ B hsupp hB
  obtain ⟨C, A, hCA⟩ := GlobalTheory.HilbertThetaSeries.GaussSum.gauss_sum_bound F κ G hG a
  obtain ⟨hTP, -, hfin⟩ := GlobalTheory.HilbertThetaSeries.qf_totPos_proper F κ G hG
  obtain ⟨-, hsc, -, hint, -, haL, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hle : ∀ z (x : κ → F), ‖Φ x * ez (QF G x) z‖ ≤ B * ‖ez (QF G x) z‖ := fun z x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hsub : ∀ z, Summable fun x : aL κ a => ‖Φ x * ez (QF G (x : κ → F)) z‖ := fun z =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hle z x) (((hCA z).1).mul_left B)
  have hzero : ∀ x, x ∉ aL κ a → Φ x = 0 := fun x hx => by
    by_contra h; exact hx (hsupp x h)
  have hsumN : ∀ z, Summable fun x : κ → F => ‖Φ x * ez (QF G x) z‖ := by
    intro z
    refine (Function.Injective.summable_iff (f := fun x : κ → F => ‖Φ x * ez (QF G x) z‖)
      (g := ((↑) : aL κ a → κ → F)) Subtype.val_injective ?_).1 (hsub z)
    intro x hx
    have : x ∉ aL κ a := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [hzero x this]
  have hsum : ∀ z, Summable fun x => Φ x * ez (QF G x) z := fun z => (hsumN z).of_norm
  have hgr : Gr (th G Φ) := by
    refine ⟨B * C, A, fun z => ?_⟩
    have e1 : ‖th G Φ z‖ ≤ ∑' x, ‖Φ x * ez (QF G x) z‖ := norm_tsum_le_tsum_norm (hsumN z)
    have e2 : ∑' x, ‖Φ x * ez (QF G x) z‖ = ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ := by
      refine (tsum_subtype_eq_of_support_subset (s := (aL κ a : Set (κ → F))) ?_).symm
      intro x hx
      by_contra h
      exact hx (by simp [hzero x h])
    have e3 : ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ ≤ ∑' x : aL κ a, B * ‖ez (QF G (x : κ → F)) z‖ :=
      Summable.tsum_le_tsum (fun x => hle z x) (hsub z) (((hCA z).1).mul_left B)
    rw [tsum_mul_left] at e3
    calc ‖th G Φ z‖ ≤ _ := e1
      _ = _ := e2
      _ ≤ _ := e3
      _ ≤ B * (C * (∏ v, (1 + ‖(z v : ℂ)‖ ^ 2) / (z v).im) ^ A) := mul_le_mul_of_nonneg_left (hCA z).2 hB0
      _ = _ := by ring
  have hQ : HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
    refine ⟨?_, fun z => ?_⟩
    · obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (.of_finite ℚ (a ^ 2))).exists_integral_multiple
      have hya : IsIntegral ℤ ((y.natAbs : F) * a ^ 2) := by
        have hy' : IsIntegral ℤ ((y : F) * a ^ 2) := by rwa [zsmul_eq_mul] at hy
        have hc : ((y.natAbs : ℕ) : F) = (((y.natAbs : ℕ) : ℤ) : F) := (Int.cast_natCast _).symm
        rw [hc]
        rcases Int.natAbs_eq y with h | h
        · rw [← h]; exact hy'
        · have h' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
          rw [h', Int.cast_neg, neg_mul]; exact hy'.neg
      refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun ξ hξ => ?_⟩
      obtain ⟨x, ⟨hxa, hxξ⟩, -⟩ : ∃ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x ≠ 0 := by
        by_contra h
        push_neg at h
        apply hξ
        beta_reduce
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        exact Finset.sum_eq_zero fun x hx => h x ((hfin a ξ).mem_toFinset.1 hx)
      obtain ⟨l, hl, rfl⟩ := (haL a x).1 hxa
      subst hxξ
      constructor
      · by_cases hx : a • l = 0
        · left; rw [hx]; simp [QF, BF]
        · right; exact hTP _ hx
      · rw [(hsc a l l).2.1, ← mul_assoc]
        exact hya.mul (hint l hl).1
    · have hfib : ∀ ξ, HasSum (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z)
          ((∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) * ez ξ z) := by
        intro ξ
        have e : (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z) = fun c : {x // QF G x = ξ} => Φ c * ez ξ z := by
          funext c; rw [c.2]
        rw [e]
        refine HasSum.mul_right _ ?_
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        have h2 : HasSum (({x | QF G x = ξ} : Set (κ → F)).indicator Φ) (∑ x ∈ (hfin a ξ).toFinset, Φ x) := by
          have h3 : ∑ x ∈ (hfin a ξ).toFinset, Φ x = ∑ x ∈ (hfin a ξ).toFinset, ({x | QF G x = ξ} : Set (κ → F)).indicator Φ x :=
            Finset.sum_congr rfl fun x hx => (Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from ((hfin a ξ).mem_toFinset.1 hx).2) _).symm
          rw [h3]
          refine hasSum_sum_of_ne_finset_zero fun x hx => ?_
          by_cases hq : QF G x = ξ
          · rw [Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from hq)]
            refine hzero x fun hxa => hx ?_
            exact (hfin a ξ).mem_toFinset.2 ⟨hxa, hq⟩
          · exact Set.indicator_of_notMem (show x ∉ ({x | QF G x = ξ} : Set (κ → F)) from hq) _
        exact (hasSum_subtype_iff_indicator (f := Φ) (s := {x | QF G x = ξ})).2 h2
      have hall : HasSum (fun x => Φ x * ez (QF G x) z) (th G Φ z) := (hsum z).hasSum
      rw [← (Equiv.sigmaFiberEquiv (QF G)).hasSum_iff] at hall
      exact hall.sigma hfib
  exact ⟨hsum, GlobalTheory.HilbertThetaSeries.QHol.hol F (th G Φ) _ hQ, hgr, hQ⟩

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_expansion | exact GlobalTheory.HilbertThetaSeries.th_expansion | (intros; apply GlobalTheory.HilbertThetaSeries.th_expansion <;> assumption)
