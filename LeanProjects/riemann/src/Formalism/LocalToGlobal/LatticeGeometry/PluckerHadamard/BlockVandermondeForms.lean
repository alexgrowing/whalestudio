import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.FlagIntegralKillsPowerSums
import Formalism.DegreeFormula.PointDegree.PowSum

noncomputable section

open Finset MvPolynomial

namespace Formalism.L2.Geo

namespace BlockVandermondeForms

open Formalism.ShimuraLimitIdentity (Pol psumAt)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def dS (τ : Ψ) (S : Finset (Fin N)) : Derivation ℝ (Pol Ψ N) (Pol Ψ N) := ∑ i ∈ S, pderiv (τ, i)

theorem dS_apply (τ : Ψ) (S : Finset (Fin N)) (P : Pol Ψ N) : dS τ S P = ∑ i ∈ S, pderiv (τ, i) P := by
  classical
  unfold dS
  refine Finset.induction_on S (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

theorem dS_X (τ : Ψ) (S : Finset (Fin N)) (σ : Ψ) (a : Fin N) :
    dS τ S (X (σ, a)) = if σ = τ ∧ a ∈ S then 1 else 0 := by
  rw [dS_apply]
  simp only [pderiv_X]
  by_cases h : σ = τ ∧ a ∈ S
  · obtain ⟨rfl, ha⟩ := h
    rw [if_pos ⟨rfl, ha⟩, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · intro h'
      exact absurd ha h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Pi.single_apply, if_neg]
    intro he
    simp only [Prod.mk.injEq] at he
    exact h ⟨he.1, by rw [he.2]; exact hi⟩

theorem d_prod_zero (D : Derivation ℝ (Pol Ψ N) (Pol Ψ N)) {ι : Type*} (s : Finset ι) (f : ι → Pol Ψ N)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by rw [Finset.prod_empty, Derivation.map_one_eq_zero]) ?_
  intro a t ha ih h
  rw [Finset.prod_insert ha, Derivation.leibniz, h a (Finset.mem_insert_self a t),
    ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), smul_zero, smul_zero, add_zero]

private theorem card_filter_fin_val_eq_card_filter_range (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin N => p i.val)).card = ((Finset.range N).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun x => if p x then 1 else 0) N

theorem card_smallBlock (N j : ℕ) : (smallBlock N j).card = N - j := by
  unfold smallBlock
  rw [card_filter_fin_val_eq_card_filter_range N (fun x => j ≤ x)]
  have e : (Finset.range N).filter (fun x => j ≤ x) = Finset.Ico j N := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e, Nat.card_Ico]

theorem card_top (N j : ℕ) (hj : j ≤ N) : (Formalism.ShimuraLimitIdentity.top N j).card = j := by
  unfold Formalism.ShimuraLimitIdentity.top
  rw [card_filter_fin_val_eq_card_filter_range N (fun x => x < j)]
  have e : (Finset.range N).filter (fun x => x < j) = Finset.range j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [e, Finset.card_range]

end BlockVandermondeForms

open BlockVandermondeForms

theorem flag_integral_kills_power_sums : FlagIntegralAnnihilatesPowerSums := by
  intro Ψ _ _ N τ k hk G
  simp only [degFlL, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]
  rw [mul_eq_zero]
  right
  have h : ∀ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (Formalism.ShimuraLimitIdentity.psumAt τ k * G).coeff (Formalism.DegreeFormula.permExp σ) =
        ∑ j : Fin N, Formalism.DegreeFormula.PPowSum.sgnP σ *
          (X (τ, (σ τ).symm j) ^ k * G).coeff (Formalism.DegreeFormula.permExp σ) := by
    intro σ
    rw [Formalism.ShimuraLimitIdentity.psumAt, Finset.sum_mul, coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm
      (fun i => Formalism.DegreeFormula.PPowSum.sgnP σ * (X (τ, i) ^ k * G).coeff (Formalism.DegreeFormula.permExp σ))).symm
  rw [Finset.sum_congr rfl fun σ _ => h σ, Finset.sum_comm]
  exact Finset.sum_eq_zero fun j _ => Formalism.DegreeFormula.PPowSum.slice τ k hk G j

namespace BlockVandermondeForms

theorem pairs_eq {N : ℕ} (S : Finset (Fin N)) :
    ∑ a ∈ S, (S.filter (fun b => a < b)).card = S.card.choose 2 := by
  refine Finset.induction_on_max S (by simp) fun m S hm ih => ?_
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  rw [Finset.sum_insert hmS, Finset.card_insert_of_notMem hmS]
  have h1 : ((insert m S).filter (fun b => m < b)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact lt_irrefl _
    · exact fun h => lt_asymm h (hm x hx)
  have h2 : ∀ a ∈ S, ((insert m S).filter (fun b => a < b)).card = (S.filter (fun b => a < b)).card + 1 := by
    intro a ha
    rw [Finset.filter_insert, if_pos (hm a ha),
      Finset.card_insert_of_notMem (fun h => hmS (Finset.mem_filter.mp h).1)]
  rw [h1, zero_add, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ih, Finset.sum_const, smul_eq_mul, mul_one,
    Nat.choose_succ_succ', Nat.choose_one_right]
  simp only [Nat.reduceAdd]
  omega

theorem add_choose_two (a b : ℕ) : (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  have hs : ∀ k : ℕ, (k + 1).choose 2 = k.choose 2 + k := fun k => by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [Nat.reduceAdd]
    omega
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, hs, hs, ih]
    ring

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem vdm_homog (τ : Ψ) (S : Finset (Fin N)) : (blockVandermondePolynomial τ S).IsHomogeneous (S.card.choose 2) := by
  unfold blockVandermondePolynomial
  rw [← pairs_eq S]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun a _ => ?_
  rw [Finset.card_eq_sum_ones]
  exact MvPolynomial.IsHomogeneous.prod _ _ _ fun b _ => (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)

end BlockVandermondeForms

end Formalism.L2.Geo
