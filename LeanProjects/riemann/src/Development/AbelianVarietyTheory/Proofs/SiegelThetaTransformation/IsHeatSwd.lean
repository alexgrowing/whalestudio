import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThHStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesOfSchwartzIsHolomorphic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.SwdHeat

open GlobalTheory.SW.EisHeat

section Linear

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem isHeat_sum {ι : Type} [Fintype ι] {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i)) : IsHeat Ψ fun Z z z' => ∑ i, D i Z z z' := by
  have h := isHeat_tsum Ψ hD fun p hp => by
    have hc : ∀ i, ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
        ‖D i q.1 q.2.1 q.2.2‖ < ‖D i p.1 p.2.1 p.2.2‖ + 1 := fun i =>
      ((hD i).1.differentiableAt
        ((isOpen_dom Ψ).mem_nhds hp)).continuousAt.norm.eventually_lt_const (lt_add_one _)
    exact ⟨_, Filter.eventually_all.2 hc, fun i => ‖D i p.1 p.2.1 p.2.2‖ + 1,
      Summable.of_finite, fun i q hq => (hq i).le⟩
  simpa only [tsum_fintype] using h

theorem isHeat_sub {D D' : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D)
    (hD' : IsHeat Ψ D') : IsHeat Ψ fun Z z z' => D Z z z' - D' Z z z' := by
  have h := isHeat_sum Ψ (ι := Bool)
    (D := fun b => bif b then D else fun Z z z' => (-1) * D' Z z z') fun b => by
      cases b
      · exact isHeat_const_mul Ψ hD' _
      · exact hD
  simpa only [Fintype.sum_bool, cond_true, cond_false, neg_one_mul, ← sub_eq_add_neg] using h

end Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem isSB_member {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · have := (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
    simpa [mul_assoc] using this
  · have := h.per Λ hΛ x ((s : E) • y) fun a => h2 _ ((Base.mem_stdL (yᵀ a)).2 fun k => hy k a)
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at this
    exact this

end GlobalTheory.SW.SwdHeat

open GlobalTheory.SW.EisHeat GlobalTheory.SW.SwdHeat in

theorem GlobalTheory.SW.isHeat_swd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → IsHeat Ψ (swd Ψ M φ) := by
  intro E _ _ _ Ψ hΨ n N hn hN M R φ hφ
  haveI := (finite_cls_and_stab E n M hφ.pos.1).1
  haveI := Fintype.ofFinite (Cls E n M)
  have h := isHeat_sum Ψ (ι := Cls E n M) fun c => isHeat_const_mul Ψ
    (isHeat_sub Ψ (GlobalTheory.T.isHeat_thH_of_isSB E Ψ hΨ n N _ (isSB_member hφ (Quot.out c).2))
      (GlobalTheory.T.eisenstein_series_of_schwartz_is_holomorphic E Ψ hΨ n N hn hN _ (isSB_member hφ (Quot.out c).2))) (wt M (Quot.out c).1 : ℂ)
  convert h using 3 with Z z
  funext z'
  exact finsum_eq_sum_of_fintype _
