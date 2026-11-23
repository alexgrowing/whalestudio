import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasisStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)

noncomputable section

namespace GlobalTheory.MainTerm

theorem sum_pow_trunc_lt_sq {C : Type} [Field C] {I ι : Type} [Fintype I] {l : ℕ} (hl : 2 ≤ l)
    (T : I → MvPowerSeries ι C) (hT : ∀ c, OrdGE 1 (T c)) (f : I → ℕ → C) (μ : ι →₀ ℕ)
    (hμ : μ.degree < l ^ 2) :
    ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ c, f c 0 * MvPowerSeries.coeff μ (T c) + ∑ c, f c 1 * MvPowerSeries.coeff μ (T c ^ l) := by
  have h1 : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ s ∈ Finset.range (μ.degree + 1 + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) := by
    rw [Finset.sum_range_succ _ (μ.degree + 1), Finset.sum_eq_zero (s := Finset.univ), add_zero]
    intro c _
    rw [(hT c).pow _ μ ((Nat.lt_succ_self _).trans (Nat.lt_pow_self (by omega))), mul_zero]
  rw [h1, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, add_comm]
  · simp
  · intro s _
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [(hT c).pow _ μ (hμ.trans_le (Nat.pow_le_pow_right (by omega) (by omega))), mul_zero]

theorem ordGE_one_of_constantCoeff {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by
  intro A hA
  have : A = 0 := (Finsupp.degree_eq_zero_iff A).1 (by omega)
  subst this
  simpa using h

theorem sum_coeff_pow_ite {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map em)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    simp
  · intro c _ hc
    have h : ∀ δ, em δ ≠ c := fun δ h => hc (Finset.mem_map.2 ⟨δ, Finset.mem_univ _, h⟩)
    simp [h, hn]

theorem coeff_low_good : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  intro C _ V d I J _ _ G S t ht N em hem
  have hl : 2 ≤ V.l := V.l_prime.two_le
  let al : I → ℕ → I → C := fun c k b =>
    if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if em j = b then 1 else 0) al
    (by intro j x; simp)
    (by intro c b; simp [al])
    (by
      intro c k x hk
      have hk' : k ≠ 0 := by omega
      simp only [al, hk', if_false, Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  set T : I → MvPowerSeries (Fin N) C := fun c => linPull (fun δ => S.tan (em δ)) (t c) with hTdef
  set z : I → MvPowerSeries (Fin N) C := fun c =>
    ∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0 with hz
  have hT : ∀ c, OrdGE 1 (T c) := fun c => ordGE_one_of_constantCoeff (h0 c)
  have hz1 : ∀ c, OrdGE 1 (z c) := fun c => by
    refine OrdGE.sum _ fun δ _ => ?_
    split_ifs
    · exact OrdGE.X δ
    · exact OrdGE.zero
  have hal1 : ∀ δ b, al (em δ) 1 b = 0 := fun δ b => by
    have : ∀ x, S.cur (em δ) 1 (Sum.inl x) = 0 := hem δ
    simp [al, Sys.co, this]
  have key : ∀ D, D + 1 ≤ V.l ^ 2 → ∀ c, OrdGE (D + 1) (T c - z c) := by
    intro D
    induction D with
    | zero => exact fun _ c => (hT c).sub (hz1 c)
    | succ D ih =>
      intro hD b A hA
      have e := h1 b A
      have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => al c s b) A (by omega)
      rw [e2] at e
      have e3 : ∀ c, MvPowerSeries.coeff A (T c ^ V.l) = MvPowerSeries.coeff A (z c ^ V.l) := fun c => by
        have := OrdGE.pow_sub_pow (hT c) (hz1 c) (ih (by omega) c) (N := V.l) (by omega) A (by omega)
        rwa [map_sub, sub_eq_zero] at this
      have e4 : ∑ c, al c 1 b * MvPowerSeries.coeff A (T c ^ V.l) = 0 := by
        simp only [e3, hz]
        rw [sum_coeff_pow_ite em (fun c => al c 1 b) (by omega)]
        simp [hal1]
      rw [e4, add_zero] at e
      rw [map_sub, sub_eq_zero]
      have e5 : ∑ c, al c 0 b * MvPowerSeries.coeff A (T c) = MvPowerSeries.coeff A (T b) := by
        simp [al]
      rw [← e5, e]
      congr 1
      refine Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp
  intro μ hμ
  refine ⟨fun c => ?_, fun κ => ?_⟩
  · have := key μ.degree hμ c μ (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  · have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => S.be c s κ) μ hμ
    have e3 : ∀ c, MvPowerSeries.coeff μ (T c ^ V.l) = MvPowerSeries.coeff μ (z c ^ V.l) := fun c => by
      have := OrdGE.pow_sub_pow (hT c) (hz1 c) (key μ.degree hμ c) (N := V.l) (by omega) μ (by omega)
      rwa [map_sub, sub_eq_zero] at this
    rw [h2 κ μ, e2]
    simp only [e3, hz]
    rw [sum_coeff_pow_ite em (fun c => S.be c 1 κ) (by omega)]
    simp [Sys.be, S.be_zero]

end GlobalTheory.MainTerm
