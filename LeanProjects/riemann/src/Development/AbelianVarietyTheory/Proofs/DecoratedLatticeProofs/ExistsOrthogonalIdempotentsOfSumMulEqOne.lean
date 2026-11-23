import Mathlib

noncomputable section

namespace GlobalTheory.AdeleIdempotents

open IsDedekindDomain NumberField

def finiteComponent (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    AdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def infiniteComponent (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    AdeleRing (𝓞 F) F →+* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_orthogonal_idempotents_of_sum_mul_eq_one (F : Type) [Field F] [NumberField F]
    (ι : Type) [Fintype ι] (f s : ι → AdeleRing (𝓞 F) F) (h : ∑ i, s i * f i = 1) :
    ∃ e t : ι → AdeleRing (𝓞 F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧
      ∀ i, t i * f i = e i := by
  classical
  have hinf : ∀ w : InfinitePlace F, ∃ i, (s i).1 w * (f i).1 w ≠ 0 := by
    intro w
    have h1 : ∑ i, (s i).1 w * (f i).1 w = 1 := by
      have := congrArg (infiniteComponent F w) h
      rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    rw [Finset.sum_eq_zero (fun i _ => hc i)] at h1
    exact zero_ne_one h1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, 1 ≤ Valued.v ((s i).2 v * (f i).2 v) := by
    intro v
    have h1 : ∑ i, (s i).2 v * (f i).2 v = 1 := by
      have := congrArg (finiteComponent F v) h
      rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    have := Valuation.map_sum_lt (Valued.v) (s := Finset.univ) (g := 1) one_ne_zero
      (fun i _ => hc i)
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  choose a ha using hinf
  choose b hb using hfin
  have hfv : ∀ v, (f (b v)).2 v ≠ 0 := by
    intro v h0
    have := hb v
    rw [h0, mul_zero, map_zero] at this
    exact absurd this (by simp)
  refine ⟨fun i => (fun w => if a w = i then 1 else 0,
      ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩),
    fun i => (fun w => if a w = i then ((f i).1 w)⁻¹ else 0,
      ⟨fun v => if b v = i then ((f i).2 v)⁻¹ else 0, (s i).2.2.mono fun v hv => by
        dsimp only
        split_ifs with hbi
        · subst hbi
          have hv' : Valued.v ((s (b v)).2 v) ≤ 1 := hv
          change Valued.v ((f (b v)).2 v)⁻¹ ≤ 1
          refine le_trans ?_ hv'
          calc Valued.v ((f (b v)).2 v)⁻¹ = Valued.v ((f (b v)).2 v)⁻¹ * 1 := (mul_one _).symm
            _ ≤ Valued.v ((f (b v)).2 v)⁻¹ * Valued.v ((s (b v)).2 v * (f (b v)).2 v) :=
              mul_le_mul' le_rfl (hb v)
            _ = Valued.v ((s (b v)).2 v) := by
              rw [← map_mul, mul_comm ((s (b v)).2 v), ← mul_assoc, inv_mul_cancel₀ (hfv v),
                one_mul]
        · exact zero_mem _⟩), ?_, ?_, ?_⟩
  · refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · refine (map_sum (infiniteComponent F w) _ _).trans ?_
      change ∑ i, (if a w = i then (1 : w.Completion) else 0) = 1
      simp
    · refine (map_sum (finiteComponent F v) _ _).trans ?_
      change ∑ i, (if b v = i then (1 : v.adicCompletion F) else 0) = 1
      simp
  · intro i j hij
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then (1 : w.Completion) else 0) * (if a w = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
    · change (if b v = i then (1 : v.adicCompletion F) else 0) * (if b v = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
  · intro i
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then ((f i).1 w)⁻¹ else 0) * (f i).1 w = (if a w = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (right_ne_zero_of_mul (ha w))
      · simp
    · change (if b v = i then ((f i).2 v)⁻¹ else 0) * (f i).2 v = (if b v = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (hfv v)
      · simp

end GlobalTheory.AdeleIdempotents
