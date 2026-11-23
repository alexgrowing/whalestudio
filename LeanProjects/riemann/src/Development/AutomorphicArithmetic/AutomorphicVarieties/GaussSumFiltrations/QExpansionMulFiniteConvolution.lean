import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.TotallyPositiveSummandsWithDenominatorFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_add_qm {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x + y) = reAt v x + reAt v y := by
  simp [reAt, map_add]

theorem ez_add_qm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x y : F) (z : Hn F) :
    ez (x + y) z = ez x z * ez y z := by
  simp only [ez, ← Complex.exp_add, reAt_add_qm, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem TP_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) :
    TP (x + y) := fun v => by rw [reAt_add_qm]; exact add_pos (hx v) (hy v)

theorem hasQ_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  intro F _ _ _ f g a b ⟨⟨D, hD, ha⟩, hf⟩ ⟨⟨E, hE, hb⟩, hg⟩
  have hfin : ∀ ξ, (Function.support fun η => a η * b (ξ - η)).Finite := by
    intro ξ
    refine (GlobalTheory.T.totallyPositive_summands_with_denominator_finite F D hD ξ).subset ?_
    intro η hη
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hη
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hη
    exact ⟨(ha η h1).1, (hb _ h2).1, (ha η h1).2⟩
  refine ⟨fun ξ => ∑ η ∈ (hfin ξ).toFinset, a η * b (ξ - η), ⟨⟨D * E, Nat.mul_pos hD hE, ?_⟩, ?_⟩,
    fun ξ => ⟨_, rfl⟩⟩
  · intro ξ hξ
    obtain ⟨η, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hne
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨p1, i1⟩ := ha η h1
    obtain ⟨p2, i2⟩ := hb _ h2
    have hsum : ξ = η + (ξ - η) := by ring
    refine ⟨?_, ?_⟩
    · rcases p1 with e1 | t1 <;> rcases p2 with e2 | t2
      · left; rw [e1, sub_zero] at e2; exact e2
      · right; rw [e1, sub_zero] at t2; exact t2
      · right; rw [sub_eq_zero] at e2; rw [e2]; exact t1
      · right; rw [hsum]; exact TP_add t1 t2
    · have hE' : IsIntegral ℤ (E : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (E : ℤ))
        simpa using this
      have hD' : IsIntegral ℤ (D : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (D : ℤ))
        simpa using this
      have : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * η) + (D : F) * ((E : F) * (ξ - η)) := by
        push_cast; ring
      rw [this]
      exact (hE'.mul i1).add (hD'.mul i2)
  · intro z
    have hu := summable_norm_iff.mpr (hf z).summable
    have hw := summable_norm_iff.mpr (hg z).summable
    have H : HasSum (fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) (f z * g z) := by
      have hs := summable_mul_of_summable_norm hu hw
      have ht := tsum_mul_tsum_of_summable_norm hu hw
      rw [(hf z).tsum_eq, (hg z).tsum_eq] at ht
      rw [ht]; exact hs.hasSum
    let e : F × F ≃ F × F :=
      { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
        left_inv := fun p => by simp, right_inv := fun q => by simp }
    have H2 := (e.hasSum_iff).mpr H
    refine H2.prod_fiberwise fun ξ => ?_
    have hx : (fun η => ((fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) ∘ e) (ξ, η)) =
        fun η => a η * b (ξ - η) * ez ξ z := by
      funext η
      simp only [Function.comp, e, Equiv.coe_fn_mk]
      have : ez ξ z = ez η z * ez (ξ - η) z := by rw [← ez_add_qm, add_sub_cancel]
      rw [this]; ring
    rw [hx, Finset.sum_mul]
    apply hasSum_sum_of_ne_finset_zero
    intro η hη
    have : a η * b (ξ - η) = 0 := by
      by_contra h
      exact hη ((hfin ξ).mem_toFinset.mpr h)
    rw [this, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_mul_finite_convolution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ), HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_mul | exact GlobalTheory.HilbertThetaSeries.hasQ_mul | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_mul <;> assumption)
