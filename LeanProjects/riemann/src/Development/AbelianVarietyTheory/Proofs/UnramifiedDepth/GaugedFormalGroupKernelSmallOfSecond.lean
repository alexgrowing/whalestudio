import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSaturatedGoodVectorsSmallCorankStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdealStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowKernel

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_sum {ι : Type} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  V.v.map_lt_sum (by simp) h

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_int_mul hb ha

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := le_of_lt h

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_div {a b : C} (hb : b ≠ 0) (h : V.v b ≤ V.v a) : V.Ge 0 (a / b) := by
  show (0 : WithTop ℝ) ≤ V.v (a / b)
  have e : V.v a = V.v (a / b) + V.v b := by rw [← V.v.map_mul, div_mul_cancel₀ a hb]
  have hb' : V.v b ≠ ⊤ := by simpa using hb
  rw [e] at h
  exact (WithTop.add_le_add_iff_right hb').mp (by simpa using h)

theorem card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by
  classical
  obtain ⟨-, W, hW, hBW⟩ := hB
  let F : Fin N ⊕ Fin M → {s // p s} → C := Sum.elim (fun ν s => A ν s.1) (fun μ s => W s.1 μ)
  have hF : LinearIndependent C F := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ s, p s → ∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ = 0 := by
      intro s hs
      have := congrFun hg ⟨s, hs⟩
      simpa [F, Fintype.sum_sum_type, Finset.sum_apply] using this
    have h2 : ∀ μ', g (Sum.inr μ') = -∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
      intro μ'
      have h3 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = 0 :=
        Finset.sum_eq_zero fun s _ => by
          by_cases hs : p s
          · rw [h1 s hs, zero_mul]
          · rw [hBp μ' s hs, mul_zero]
      have h4 : ∑ s, (∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = g (Sum.inr μ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ μ, ∑ s, g (Sum.inr μ) * W s μ * B μ' s = g (Sum.inr μ) * if μ' = μ then 1 else 0 := by
          intro μ
          rw [← hBW μ' μ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp [this]
      have h5 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s) * B μ' s = ∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => by ring
      simp only [add_mul, Finset.sum_add_distrib] at h3
      rw [h4, h5] at h3
      linear_combination h3
    have h6 : ∀ ν, g (Sum.inl ν) = 0 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ν1, hν1⟩ := hc
      obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (g (Sum.inl ν)))
        ⟨ν1, Finset.mem_univ _⟩
      have h0 : g (Sum.inl ν0) ≠ 0 := by
        intro h0
        have := hmin ν1 (Finset.mem_univ _)
        rw [h0, V.v.map_zero, top_le_iff] at this
        exact hν1 (by simpa using this)
      have hint : ∀ ν, V.Ge 0 (g (Sum.inl ν) / g (Sum.inl ν0)) := fun ν =>
        ge_div h0 (hmin ν (Finset.mem_univ _))
      have key := hA (fun ν => g (Sum.inl ν) / g (Sum.inl ν0)) hint (fun s => by
        by_cases hs : p s
        · have e : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
              ∑ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) * W s μ := by
            have e1 : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
                (g (Sum.inl ν0))⁻¹ * ∑ ν, g (Sum.inl ν) * A ν s := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e2 : ∀ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) =
                -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) := by
              intro μ
              rw [h2 μ, mul_neg, neg_neg, Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e3 : ∑ μ, -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) * W s μ =
                -((g (Sum.inl ν0))⁻¹ * ∑ μ, g (Sum.inr μ) * W s μ) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun ν _ => by ring
            simp only [e2]
            rw [e1, e3]
            linear_combination (g (Sum.inl ν0))⁻¹ * h1 s hs
          rw [e]
          exact mm_sum fun μ _ => mm_mul_int (mm_sum fun ν _ => mm_int_mul (hint ν) (hAB ν μ)) (hW s μ)
        · simp only [hAp _ s hs, mul_zero, Finset.sum_const_zero]
          exact mm_zero) ν0
      simp only [div_self h0] at key
      exact not_mm_one key
    intro i
    cases i with
    | inl ν => exact h6 ν
    | inr μ => rw [h2 μ]; simp [h6]
  have := hF.fintype_card_le_finrank
  simpa [Fintype.card_subtype] using this

theorem mm_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h

theorem independenceBoundCondition_of_rankMaximalCondition : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  intro C _ V d _ I _ κ _ X hL hR H h2 hA g a ha N w x hgood hV hind
  classical
  haveI := hL.closed
  have hstep := CharacteristicFromRanks.alt_step X.big hR.big_compl hA
  have hb1 : X.big (1 - g) (a + 1) := (hR.big_compl g (a + 1)).2 fun h => (hstep g a).1 h ha
  have hb2 : ¬ X.big (1 - g) (a + 1 + 1) := fun h => (hstep (1 - g) (a + 1)).1 h hb1
  obtain ⟨M, w', x', hgood', hsupp, hsat, hcard⟩ :=
    GlobalTheory.T.exists_saturated_good_vectors_small_corank C V d (I (1 - g)) (JJ I (1 - g)) (RawChart.cart (H (1 - g))) (a + 1)
  have c1 := hR.rk_big (1 - g) (a + 1) hb1
  have c2 := hR.rk_small (1 - g) (a + 1 + 1) hb2
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  have hind' : IndepMod V (fun ν => (RawChart.cart (H g)).c0' (x ν)) := by
    intro c hc hmm
    choose co hco using fun ν => IsAlgClosed.exists_pow_nat_eq (c ν) (Nat.pos_of_ne_zero hl)
    have hcoi : ∀ ν, V.Ge 0 (co ν) := fun ν => ge_of_pow hl (by rw [hco]; exact hc ν)
    have hG := Cart.Good.comb Finset.univ (fun ν _ => hcoi ν) (fun ν _ => hgood ν)
    have h3 := h2 hA g a ha _ _ hG (fun q => by
      rw [Cart.c0'_comb]
      simp only [hco]
      exact hmm q)
    have h4 := hind co hcoi (fun k => by simpa [Finset.sum_apply] using h3 k)
    intro ν
    rw [← hco ν]
    exact mm_pow hl (h4 ν)
  have key := card_add_le (V := V) (fun c : I (1 - g) => X.ty (1 - g) c = a + 1)
    (fun ν => (RawChart.cart (H g)).c0' (x ν)) w' hind'
    (fun ν s hs => by
      have := (hgood ν).1.2.2 1 (Sum.inr s) (by simpa [RawChart.cart, RawChart.tyC] using hs)
      simp [Cart.c0', this])
    hsat (fun μ s hs => hsupp μ s hs)
    (fun ν μ => GlobalTheory.T.goodCurves_pairing_mem_maxIdeal C V d I κ X hL H g a (a + 1) (w ν) (x ν) (w' μ) (x' μ) (hgood ν) (hgood' μ) (hV ν))
  have hcard' : X.n + X.j ≤ M + X.j' := by
    rw [← c1, ← c2]
    convert hcard <;> rfl
  have key' : N + M ≤ X.n + X.j := by
    rw [← c1]
    convert key
  omega

end GlobalTheory.RowKernel
