import Formalism.LocalToGlobal.CharacterGerms.RowTieValCr

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

def lin1 {σ : Type} (f : MvPowerSeries σ C) (j : σ) : C := MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C j f)

theorem linear_coeff_eq_coeff_single {σ : Type} (f : MvPowerSeries σ C) (j : σ) : lin1 f j = MvPowerSeries.coeff (Finsupp.single j 1) f := by
  unfold lin1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem linear_coeff_subst_chain_rule {σ : Type} [Fintype σ] {A : σ → MvPowerSeries τ C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (f : MvPowerSeries σ C) (j : τ) :
    lin1 (MvPowerSeries.subst A f) j = ∑ k, lin1 (A k) j * lin1 f k := by
  have hs : MvPowerSeries.HasSubst A := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hA
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hA
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hA s]; exact IsNilpotent.zero)

  have hmul : ∀ P R : MvPowerSeries τ C, MvPowerSeries.constantCoeff P = 0 →
      MvPowerSeries.constantCoeff R = 0 → MvPowerSeries.coeff (Finsupp.single j 1) (P * R) = 0 := by
    intro P R hP hR
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    first
      | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      | rw [Finset.mem_antidiagonal] at hab
      | simp only [Finset.mem_antidiagonal] at hab
    by_cases ha : ab.1 = 0
    · rw [ha, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hP, zero_mul]
    · have hb : ab.2 = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, ab.1 i ≠ 0 := by
          by_contra h
          push_neg at h
          exact ha (Finsupp.ext h)
        have hij : i = j := by
          by_contra hne
          have := congrArg (fun d => d i) hab
          simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hne, if_false] at this
          omega
        subst hij
        ext t
        have := congrArg (fun d => d t) hab
        by_cases ht : t = i
        · subst ht
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        · simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm ht, if_false] at this
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
      rw [hb, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hR, mul_zero]

  have hpow : ∀ (a : σ) (b : ℕ), b ≠ 0 → MvPowerSeries.constantCoeff (A a ^ b) = 0 := by
    intro a b hb
    rw [map_pow, hA a, zero_pow hb]
  have hprod : ∀ d : σ →₀ ℕ, d ≠ 0 → MvPowerSeries.constantCoeff (d.prod fun s e => A s ^ e) = 0 ∧
      ((∀ k, d ≠ Finsupp.single k 1) →
        MvPowerSeries.coeff (Finsupp.single j 1) (d.prod fun s e => A s ^ e) = 0) := by
    intro d
    refine Finsupp.induction d ?_ ?_
    · intro h
      exact absurd rfl h
    · intro a b g hag hb ih _
      have hP : (Finsupp.single a b + g).prod (fun s e => A s ^ e) = A a ^ b * g.prod (fun s e => A s ^ e) := by
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          show (Finsupp.single a b).prod (fun s e => A s ^ e) = A a ^ b from Finsupp.prod_single_index (pow_zero _)]
      rw [hP]
      refine ⟨by rw [map_mul, hpow a b hb, zero_mul], fun hnot => ?_⟩
      by_cases hg : g = 0
      · subst hg
        rw [Finsupp.prod_zero_index, mul_one]
        have hb1 : b ≠ 1 := by
          intro h1
          subst h1
          exact hnot a (add_zero _)
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        rw [pow_succ]
        exact hmul _ _ (hpow a c (by omega)) (hA a)
      · exact hmul _ _ (hpow a b hb) (ih hg).1
  rw [linear_coeff_eq_coeff_single, MvPowerSeries.coeff_subst hs]
  have hsupp : (Function.support fun d : σ →₀ ℕ => MvPowerSeries.coeff d f •
      MvPowerSeries.coeff (Finsupp.single j 1) (d.prod fun s e => A s ^ e)) ⊆
      ↑(Finset.univ.image fun k : σ => Finsupp.single k 1) := by
    intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hne
    push_neg at hne
    apply hd
    by_cases h0 : d = 0
    · subst h0
      rw [Finsupp.prod_zero_index, MvPowerSeries.coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
        smul_zero]
    · rw [(hprod d h0).2 (fun k h => hne k h.symm), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun k _ l _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [show (Finsupp.single k 1).prod (fun s e => A s ^ e) = A k ^ 1 from Finsupp.prod_single_index (pow_zero _),
    pow_one, smul_eq_mul, linear_coeff_eq_coeff_single, linear_coeff_eq_coeff_single, mul_comm]

theorem linear_coeff_X_eq_ite {σ : Type} (m j : σ) : lin1 (MvPowerSeries.X m : MvPowerSeries σ C) j = if m = j then 1 else 0 := by
  rw [linear_coeff_eq_coeff_single, MvPowerSeries.coeff_X]
  by_cases h : m = j
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h ((Finsupp.single_left_inj one_ne_zero).mp h').symm

theorem lin_of_add (f : MvPowerSeries (Fin dd) C) (h0 : MvPowerSeries.constantCoeff f = 0)
    (hadd : MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f =
      MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd)) f +
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f) :
    f = ∑ j, lin1 f j • (MvPowerSeries.X j : MvPowerSeries (Fin dd) C) := by
  have cS : ∀ m : Fin dd, MvPowerSeries.constantCoeff
      (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) = 0 := fun m => by
    rw [map_add, cc_X, cc_X, add_zero]
  set K : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C := P2 MvPowerSeries.X (fun _ => 0) with hK
  have cK : ∀ q, MvPowerSeries.constantCoeff (K q) = 0 := constantCoeff_pair_substitution (fun _ => cc_X _) (fun _ => map_zero _)
  have hder : ∀ i, MvPowerSeries.pderiv C i f = MvPowerSeries.C (lin1 f i) := by
    intro i
    have h := congrArg (fun G => MvPowerSeries.subst K (MvPowerSeries.pderiv C ((1 : Fin 2), i) G)) hadd
    beta_reduce at h
    rw [map_add, pderiv_subst (og cS), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
      subst_add' cK, subst_sum cK, subst_sum cK, subst_sum cK] at h
    have h1 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv C ((1 : Fin 2), i)
        (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv C m f)) = if m = i then MvPowerSeries.pderiv C i f else 0 := by
      intro m
      rw [map_add, MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_add]
      by_cases hm : m = i
      · subst hm
        rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst cS cK, if_pos rfl]
        have : (fun s : Fin dd => MvPowerSeries.subst K
            (MvPowerSeries.X ((0 : Fin 2), s) + MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = MvPowerSeries.X := by
          funext s
          rw [subst_add' cK, subst_X cK, subst_X cK]
          show MvPowerSeries.X s + 0 = _
          rw [add_zero]
        rw [this, MvPowerSeries.subst_self]
        rfl
      · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hm (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' cK, if_neg hm]
    have h2 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv C ((1 : Fin 2), i)
        (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv C m f)) = 0 := by
      intro m
      rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul, subst_zero' cK]
    have h3 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv C ((1 : Fin 2), i)
        (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv C m f)) = if m = i then MvPowerSeries.C (lin1 f i) else 0 := by
      intro m
      by_cases hm : m = i
      · subst hm
        rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) cK, if_pos rfl]
        have : (fun s : Fin dd => MvPowerSeries.subst K (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = fun _ => 0 := by
          funext s
          rw [subst_X cK]
          rfl
        rw [this, subst_zeroPt]
        rfl
      · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hm (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' cK, if_neg hm]
    rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_congr rfl fun m _ => h2 m,
      Finset.sum_congr rfl fun m _ => h3 m, Finset.sum_const_zero, zero_add, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
    simpa using h
  ext μ
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, MvPowerSeries.coeff_X]
  by_cases hμ : μ = 0
  · subst hμ
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => by simpa using congrArg (fun x => x j) h), mul_zero]
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hμ (Finsupp.ext hcon)
    obtain ⟨ν, rfl⟩ : ∃ ν : Fin dd →₀ ℕ, μ = ν + Finsupp.single i 1 :=
      ⟨μ - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))).symm⟩
    have hc := congrArg (MvPowerSeries.coeff ν) (hder i)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C] at hc
    have hne : ((ν i : C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (ν i)
    by_cases hν : ν = 0
    · subst hν
      rw [zero_add, Finset.sum_eq_single i]
      · rw [if_pos rfl, mul_one, linear_coeff_eq_coeff_single]
      · intro j _ hj
        rw [if_neg fun h => hj (Finsupp.single_left_injective one_ne_zero h).symm, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hν] at hc
      rw [(mul_eq_zero.1 hc).resolve_right hne]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg, mul_zero]
      intro h
      have hd := congrArg Finsupp.degree h
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at hd
      exact hν ((Finsupp.degree_eq_zero_iff _).1 (by omega))

end VP

end Formalism.L2.FormalSeriesBounds
