import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelExpNonneg
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FlagZ.AbelSum

theorem sum_neg_smul_sub {G : Type*} [AddCommGroup G] (N : ℕ) (lam : Fin N → ℤ) (F : Fin (N + 1) → G) :
    ∑ i : Fin N, (-lam i) • (F i.castSucc - F i.succ) =
      ∑ l : Fin (N + 1), (if h : 0 < (l : ℕ) ∧ (l : ℕ) < N then lam ⟨(l : ℕ) - 1, by omega⟩ - lam ⟨l, h.2⟩ else 0) • F l +
        ((if h : 0 < N then -lam ⟨0, h⟩ else 0) • F 0 +
          (if h : 0 < N then lam ⟨N - 1, by omega⟩ else 0) • F (Fin.last N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp

  have hA : ∑ i : Fin N, (-lam i) • F i.castSucc =
      ∑ l : Fin (N + 1), (if h : (l : ℕ) < N then -lam ⟨l, h⟩ else 0) • F l := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, zero_smul,
      add_zero, Fin.eta]
  have hB : ∑ i : Fin N, (-lam i) • F i.succ =
      ∑ l : Fin (N + 1), (if h : 0 < (l : ℕ) then -lam ⟨(l : ℕ) - 1, by omega⟩ else 0) • F l := by
    rw [Fin.sum_univ_succ, dif_neg (by simp), zero_smul, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos (by simp)]
    congr 2
  rw [Finset.sum_congr rfl fun i _ => smul_sub _ _ _, Finset.sum_sub_distrib, hA, hB, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  rw [dif_pos hN, dif_pos hN]
  have e0 : (-lam ⟨0, hN⟩) • F 0 = ∑ l : Fin (N + 1), (if l = 0 then -lam ⟨0, hN⟩ else 0) • F l := by
    simp [ite_smul]
  have e1 : lam ⟨N - 1, by omega⟩ • F (Fin.last N) =
      ∑ l : Fin (N + 1), (if l = Fin.last N then lam ⟨N - 1, by omega⟩ else 0) • F l := by
    simp [ite_smul]
  rw [e0, e1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← add_smul]
  congr 1
  have hl := l.is_lt
  by_cases h0 : (l : ℕ) = 0
  · have : l = 0 := Fin.ext h0
    subst this
    have : (0 : Fin (N + 1)) ≠ Fin.last N := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    simp [this, hN]
  by_cases hL : (l : ℕ) = N
  · have : l = Fin.last N := Fin.ext hL
    subst this
    have : Fin.last N ≠ 0 := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    simp [this, hN]
  · have hne0 : l ≠ 0 := fun h => h0 (by simp [h])
    have hneL : l ≠ Fin.last N := fun h => hL (by simp [h])
    have hpos : 0 < (l : ℕ) := Nat.pos_of_ne_zero h0
    have hlt : (l : ℕ) < N := by omega
    simp only [hne0, hneL, if_false, dif_pos hpos, dif_pos hlt, dif_pos (And.intro hpos hlt)]
    ring

end GlobalTheory.FlagZ.AbelSum

namespace GlobalTheory.FlagZ.AbelSum

theorem icls_wtLine_eq_abel : ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ), ∃ e₀ e₁ : ι → ℤ,
    (wtLine lam).icls = ∑ x : ι × Fin (N + 1), abelExp lam x • (flDet x.1 x.2 : GlobalTheory.HermLB (flStr ι N)).icls +
      ∑ τ, (e₀ τ • (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).icls +
        e₁ τ • (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).icls) := by
  intro ι _ N lam
  refine ⟨fun τ => if h : 0 < N then -lam τ ⟨0, h⟩ else 0, fun τ => if h : 0 < N then lam τ ⟨N - 1, by omega⟩ else 0, ?_⟩
  rw [wtLine, icls_comb, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e (i : Fin N) : (grLine (ι := ι) (N := N) (τ, i)).icls =
      (flDet (ι := ι) (N := N) τ i.castSucc).icls - (flDet (ι := ι) (N := N) τ i.succ).icls := by
    rw [grLine, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
  simp only [e]
  exact sum_neg_smul_sub N (lam τ) fun l => (flDet (ι := ι) (N := N) τ l).icls

end GlobalTheory.FlagZ.AbelSum
