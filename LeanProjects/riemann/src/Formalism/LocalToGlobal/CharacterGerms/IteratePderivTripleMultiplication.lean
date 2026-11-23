import Formalism.LocalToGlobal.CharacterGerms.PderivTripleMultiplicationMaximal

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

def Phi (V : VF C) (u : Fin dd → C) (f : PS C 3 dd) (γ : Fin 2 × Fin dd →₀ ℕ) : C :=
  ∑ i, u i ^ V.l * coeff (ix i V.l γ) f

def Tk (f : PS C 3 dd) (k : Fin dd) : PS C 3 dd :=
  fun p => if (∀ j : Fin dd, j < k → p ((0 : Fin 3), j) = 0) then coeff (p + Finsupp.single ((0 : Fin 3), k) 1) f else 0

theorem Tk_int {f : PS C 3 dd} (hf : IntS V f) (k : Fin dd) : IntS V (Tk f k) := by
  intro μ
  show V.Ge 0 (if (∀ j : Fin dd, j < k → μ ((0 : Fin 3), j) = 0) then
    coeff (μ + Finsupp.single ((0 : Fin 3), k) 1) f else 0)
  split_ifs
  · exact hf _
  · unfold VF.Ge
    simp [AddValuation.map_zero]

theorem decomp {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) : f = 1 + ∑ k, X ((0 : Fin 3), k) * Tk f k := by
  classical
  ext p
  rw [map_add, MvPowerSeries.coeff_one, map_sum]
  have hX : ∀ k, coeff p (X ((0 : Fin 3), k) * Tk f k) =
      if Finsupp.single ((0 : Fin 3), k) 1 ≤ p then
        coeff (p - Finsupp.single ((0 : Fin 3), k) 1) (Tk f k) else 0 := by
    intro k
    rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
  simp only [hX]
  by_cases hfree : ∀ j, p ((0 : Fin 3), j) = 0
  · rw [coeff_free h1 hfree, Finset.sum_eq_zero, add_zero]
    intro k _
    rw [if_neg]
    rw [Finsupp.single_le_iff, hfree k]
    omega
  · push_neg at hfree
    set S := Finset.univ.filter (fun j : Fin dd => p ((0 : Fin 3), j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hfree
      exact ⟨j, by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj⟩
    set k0 := S.min' hS with hk0
    have hk0S : k0 ∈ S := S.min'_mem hS
    have hk0p : p ((0 : Fin 3), k0) ≠ 0 := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hk0S
      exact hk0S
    have hmin : ∀ j, j < k0 → p ((0 : Fin 3), j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne
      exact absurd hj (not_lt.mpr (S.min'_le j hjS))
    have hp0 : p ≠ 0 := by
      intro h
      apply hk0p
      rw [h]
      rfl
    have hle0 : Finsupp.single ((0 : Fin 3), k0) 1 ≤ p := by
      rw [Finsupp.single_le_iff]
      omega
    rw [if_neg hp0, zero_add, Finset.sum_eq_single k0]
    · rw [if_pos hle0]
      show coeff p f = (if (∀ j : Fin dd, j < k0 →
          (p - Finsupp.single ((0 : Fin 3), k0) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j) = 0) then
          coeff (p - Finsupp.single ((0 : Fin 3), k0) 1 + Finsupp.single ((0 : Fin 3), k0) 1) f else 0)
      rw [if_pos, tsub_add_cancel_of_le hle0]
      intro j hj
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg, hmin j hj]
      all_goals first
        | rfl
        | (intro h
           simp only [Prod.mk.injEq, true_and] at h
           subst h
           exact lt_irrefl _ hj)
    · intro k _ hk
      by_cases hle : Finsupp.single ((0 : Fin 3), k) 1 ≤ p
      · rw [if_pos hle]
        show (if (∀ j : Fin dd, j < k →
            (p - Finsupp.single ((0 : Fin 3), k) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j) = 0) then
            coeff (p - Finsupp.single ((0 : Fin 3), k) 1 + Finsupp.single ((0 : Fin 3), k) 1) f else 0) = 0
        rw [if_neg]
        intro hall
        have hkS : k ∈ S := by
          simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Finsupp.single_le_iff] at hle
          omega
        have hk0k : k0 < k := lt_of_le_of_ne (S.min'_le k hkS) (Ne.symm hk)
        have h2 := hall k0 hk0k
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg] at h2
        · exact hk0p (by omega)
        · intro h
          simp only [Prod.mk.injEq, true_and] at h
          exact hk h
      · rw [if_neg hle]
    · intro h
      exact absurd (Finset.mem_univ k0) h

theorem QQ_expand (Y : FBChart C V O dd) :
    QQ Y = 1 + ∑ k, m3 Y.B.G V.l k * ev ![m3 Y.B.G V.l, p3 1, p3 2] (Tk Y.B.ph2 k) := by
  have hz := constant_zero_triple_multiplication Y
  conv_lhs => rw [QQ, decomp (second_pairing_restrict_one Y)]
  rw [PartialDerivEval.ev_add hz, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_one, PartialDerivEval.ev_sum hz]
  simp only [PartialDerivEval.ev_mul hz, PartialDerivEval.ev_X hz]
  rfl

theorem triple_multiplication_pderiv_other (Y : FBChart C V O dd) (k : Fin dd) (s : Fin 3 × Fin dd) (hs : s.1 ≠ 0) :
    pderiv C s (m3 Y.B.G V.l k) = 0 := by
  simp only [m3]
  rw [pderiv_eval_single (fun j => by simp [p3, pt])]
  apply Finset.sum_eq_zero
  intro j _
  simp only [p3, pderiv_pt]
  rw [if_neg (fun h => hs (congrArg Prod.fst h).symm), mul_zero]

theorem triple_multiplication_first_only (Y : FBChart C V O dd) (k : Fin dd) (p : Fin 3 × Fin dd →₀ ℕ) (s : Fin 3 × Fin dd)
    (hs : s.1 ≠ 0) (hp : p s ≠ 0) : coeff p (m3 Y.B.G V.l k) = 0 := by
  have h := congrArg (coeff (p - Finsupp.single s 1)) (triple_multiplication_pderiv_other Y k s hs)
  rw [MvPowerSeries.coeff_pderiv, map_zero] at h
  have hle : Finsupp.single s 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp
  rw [tsub_add_cancel_of_le hle] at h
  exact (mul_eq_zero.mp h).resolve_right (Nat.cast_add_one_ne_zero _)

private theorem pderiv_ev_p3_zero_eq_ev_pderiv (i : Fin dd) (g : PS C 1 dd) :
    pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] g) =
      ev ![(p3 0 : Pt C 3 dd)] (pderiv C ((0 : Fin 1), i) g) := by
  rw [pderiv_eval_single (fun j => by simp [p3, pt])]
  simp [p3, pderiv_pt, Finset.sum_ite_eq']

theorem iterate_pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) (L : ℕ) :
    (pderiv C ((0 : Fin 3), i))^[L] (m3 Y.B.G V.l k) =
      ev ![(p3 0 : Pt C 3 dd)] ((pderiv C ((0 : Fin 1), i))^[L] (mulL Y.B.G.F V.l k)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_ev_p3_zero_eq_ev_pderiv,
      ← Function.iterate_succ_apply' (pderiv C ((0 : Fin 1), i))]

private theorem coeff_iterate_pderiv_eq_coeff_add_single_mul_prod {σ : Type} (i : σ) (L : ℕ) : ∀ (f : MvPowerSeries σ C) (μ : σ →₀ ℕ),
    coeff μ ((pderiv C i)^[L] f) =
      coeff (μ + Finsupp.single i L) f * ∏ t ∈ Finset.range L, ((μ i : C) + t + 1) := by
  induction L with
  | zero =>
    intro f μ
    simp
  | succ L ih =>
    intro f μ
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv, Finset.prod_range_succ]
    have e : μ + Finsupp.single i L + Finsupp.single i 1 = μ + Finsupp.single i (L + 1) := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [e]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring

theorem coeff_triple_multiplication_single (Y : FBChart C V O dd) (k i : Fin dd) (L : ℕ) :
    coeff (Finsupp.single ((0 : Fin 3), i) L) (m3 Y.B.G V.l k) =
      coeff (Finsupp.single ((0 : Fin 1), i) L) (mulL Y.B.G.F V.l k) := by
  have hz : Z0 (![(p3 0 : Pt C 3 dd)] : Fin 1 → Pt C 3 dd) := by
    intro j i
    fin_cases j
    simp [p3, pt]
  have h1 := coeff_iterate_pderiv_eq_coeff_add_single_mul_prod ((0 : Fin 3), i) L (m3 Y.B.G V.l k) 0
  have h2 := coeff_iterate_pderiv_eq_coeff_add_single_mul_prod ((0 : Fin 1), i) L (mulL Y.B.G.F V.l k) 0
  rw [iterate_pderiv_triple_multiplication] at h1
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero] at h1 h2
  have hP : ∏ t ∈ Finset.range L, ((t : C) + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => Nat.cast_add_one_ne_zero t)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PartialDerivEval.constantCoeff_ev hz,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h2] at h1
  exact (mul_right_cancel₀ hP h1).symm

theorem triple_multiplication_frobenius (Y : FBChart C V O dd) (k : Fin dd) : FrobX V (m3 Y.B.G V.l k) := by
  exact frobX_of (triple_multiplication_integral Y.B.G Y.intF V.l k) (fun j => pderiv_triple_multiplication_maximal Y k j)

private theorem mm_zero_of_vf : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_add_character_germs {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_sum_character_germs {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) :=
  Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_character_germs hx hy) mm_zero_of_vf h

private theorem mm_mul_ge_zero_right {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem m3mul (Y : FBChart C V O dd) (k i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {G : PS C 3 dd} (hG : IntS V G) :
    V.MM (coeff (ix i V.l γ) (m3 Y.B.G V.l k * G) -
      coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * coeff (γ.mapDomain (up 2)) G) := by
  classical
  set N := ix i V.l γ with hN
  have hl0 : 0 < V.l := V.l_prime.pos
  have hNi : N ((0 : Fin 3), i) = V.l := by rw [hN, index_raise_first, if_pos rfl]
  have key : ∀ a : Fin 3 × Fin dd →₀ ℕ, a ≤ N → a ≠ Finsupp.single ((0 : Fin 3), i) V.l →
      V.MM (coeff a (m3 Y.B.G V.l k)) := by
    intro a ha hne
    by_cases hz : ∃ s : Fin 3 × Fin dd, s.1 ≠ 0 ∧ a s ≠ 0
    · obtain ⟨s, hs, has⟩ := hz
      rw [triple_multiplication_first_only Y k a s hs has]
      exact mm_zero_of_vf
    · push_neg at hz
      have hx : ∀ j, j ≠ i → a ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
      by_cases hd : V.l ∣ a ((0 : Fin 3), i)
      · have hle : a ((0 : Fin 3), i) ≤ V.l := by
          have := ha ((0 : Fin 3), i)
          rwa [hNi] at this
        have h01 : a ((0 : Fin 3), i) = 0 ∨ a ((0 : Fin 3), i) = V.l := by
          obtain ⟨q, hq⟩ := hd
          rcases q with _ | _ | q
          · left
            simpa using hq
          · right
            simpa using hq
          · exfalso
            have h3 := hq ▸ hle
            nlinarith
        have hext : ∀ c : ℕ, a ((0 : Fin 3), i) = c → a = Finsupp.single ((0 : Fin 3), i) c := by
          intro c hc
          ext ⟨kk, j⟩
          induction kk using Fin.cases with
          | zero =>
            rw [Finsupp.single_apply]
            by_cases hj : j = i
            · subst hj
              rw [if_pos rfl]
              exact hc
            · rw [if_neg (fun h => hj (congrArg Prod.snd h).symm), hx j hj]
          | succ kk' =>
            rw [Finsupp.single_apply, if_neg (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h).symm)]
            exact hz _ (Fin.succ_ne_zero _)
        rcases h01 with h0 | hL
        · rw [hext 0 h0, Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, triple_multiplication_constantCoeff]
          exact mm_zero_of_vf
        · exact absurd (hext V.l hL) hne
      · exact triple_multiplication_frobenius Y k a ⟨i, hd⟩
  rw [MvPowerSeries.coeff_mul]
  have hx0 : (Finsupp.single ((0 : Fin 3), i) V.l, γ.mapDomain (up 2)) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal, hN]
    rfl
  rw [← Finset.add_sum_erase _ _ hx0]
  dsimp only
  rw [coeff_triple_multiplication_single Y k i V.l, add_sub_cancel_left]
  apply mm_sum_character_germs
  intro x hx
  obtain ⟨hne, hxa⟩ := Finset.mem_erase.mp hx
  have hxa' := Finset.HasAntidiagonal.mem_antidiagonal.mp hxa
  have ha : x.1 ≤ N := by
    rw [← hxa']
    exact le_self_add
  have hne1 : x.1 ≠ Finsupp.single ((0 : Fin 3), i) V.l := by
    intro h1
    apply hne
    have h2 : x.2 = γ.mapDomain (up 2) := by
      have h3 := hxa'
      rw [h1, hN] at h3
      unfold ix at h3
      exact add_left_cancel h3
    exact Prod.ext h1 h2
  exact mm_mul_ge_zero_right (key x.1 ha hne1) (hG x.2)

private theorem intS_one' {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) := by
  intro μ
  unfold VF.Ge
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · simp [AddValuation.map_one]
  · simp [AddValuation.map_zero]

private theorem intS_mul_character_germs' {V : VF C} {σ : Type} {f g : MvPowerSeries σ C} (hf : IntS V f)
    (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  unfold VF.Ge
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  have h1 := hf x.1
  have h2 := hg x.2
  unfold VF.Ge at h1 h2
  simpa using add_le_add h1 h2

private theorem intS_pow' {V : VF C} {σ : Type} {f : MvPowerSeries σ C} (hf : IntS V f) (k : ℕ) :
    IntS V (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact intS_one'
  | succ k ih => rw [pow_succ]; exact intS_mul_character_germs' ih hf

private theorem intS_ev_of_z0_of_intS {V : VF C} {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a)
    (hi : ∀ k j, IntS V (a k j)) {f : PS C m dd} (hf : IntS V f) : IntS V (ev a f) := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  intro e
  show V.Ge 0 (coeff e (MvPowerSeries.subst (fun p : Fin m × Fin dd => a p.1 p.2) f))
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs f e)]
  unfold VF.Ge
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have hd : IntS V (d.prod fun s k => (fun p : Fin m × Fin dd => a p.1 p.2) s ^ k) := by
    unfold Finsupp.prod
    exact Finset.prod_induction _ (fun g => IntS V g) (fun x y hx hy => intS_mul_character_germs' hx hy) intS_one'
      (fun s _ => intS_pow' (hi s.1 s.2) _)
  have h1 := hf d
  have h2 := hd e
  unfold VF.Ge at h1 h2
  simpa using add_le_add h1 h2

private theorem mm_mul_of_ge_zero_of_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [AddValuation.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := by simpa using ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem phiQ (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (hV1 : Y.FirstVanishingAt u)
    (γ : Fin 2 × Fin dd →₀ ℕ) : V.MM (Phi V u (QQ Y) γ) := by
  have hzi : ∀ k i, IntS V ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k i) := by
    intro k i
    fin_cases k
    · exact triple_multiplication_integral Y.B.G Y.intF V.l i
    · exact triple_coordinate_integral 1 i
    · exact triple_coordinate_integral 2 i
  have hIT : ∀ k, IntS V (ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)) :=
    fun k => intS_ev_of_z0_of_intS (constant_zero_triple_multiplication Y) hzi (Tk_int Y.intPh2 k)
  have alg : ∀ (A : Fin dd → Fin dd → C) (B : Fin dd → Fin dd → C) (t : Fin dd → C) (w : Fin dd → C),
      ∑ i, w i * ∑ k, A i k = ∑ i, ∑ k, w i * (A i k - B k i * t k) + ∑ k, t k * ∑ i, B k i * w i := by
    intro A B t w
    have h1 : ∀ i, w i * ∑ k, A i k = ∑ k, w i * (A i k - B k i * t k) + ∑ k, w i * (B k i * t k) := by
      intro i
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
      Finset.sum_comm (f := fun i k => w i * (B k i * t k))]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hA : ∀ i, coeff (ix i V.l γ) (1 + ∑ k, m3 Y.B.G V.l k *
      ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)) =
      ∑ k, coeff (ix i V.l γ) (m3 Y.B.G V.l k * ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd)
        (Tk Y.B.ph2 k)) := by
    intro i
    rw [map_add, map_sum, MvPowerSeries.coeff_one, if_neg, zero_add]
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  unfold Phi
  rw [QQ_expand Y]
  simp only [hA]
  rw [alg _ (fun k i => coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k))
    (fun k => coeff (γ.mapDomain (up 2)) (ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)))]
  apply mm_add_character_germs
  · apply mm_sum_character_germs
    intro i _
    apply mm_sum_character_germs
    intro k _
    have hul : V.Ge 0 (u i ^ V.l) := by
      unfold VF.Ge
      rw [AddValuation.map_pow]
      have h0 : (0 : WithTop ℝ) ≤ V.v (u i) := by simpa [VF.Ge] using hu i
      simpa using nsmul_nonneg h0 V.l
    exact mm_mul_of_ge_zero_of_mm hul (m3mul Y k i γ (hIT k))
  · apply mm_sum_character_germs
    intro k _
    exact mm_mul_of_ge_zero_of_mm (hIT k _) (hV1 k)

private theorem v_natCast_nonneg_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

private theorem mm_add_of_both {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_finset_sum {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_both hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_add_pow_l_sub_pow_l_sub_pow_l {y z : C} (hy : V.Ge 0 y) (hz : V.Ge 0 z) :
    V.MM ((y + z) ^ V.l - y ^ V.l - z ^ V.l) := by
  obtain ⟨n, hn⟩ : ∃ n, V.l = n + 1 := ⟨V.l - 1, (Nat.succ_pred_eq_of_pos V.l_prime.pos).symm⟩
  have hpr : (n + 1).Prime := hn ▸ V.l_prime
  have hvl : V.v ((n + 1 : ℕ) : C) = 1 := by
    rw [← hn]
    exact V.v_l
  rw [hn, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero, mul_one, one_mul,
    Nat.cast_one]
  have e : ∀ A B D : C, A + B + D - D - B = A := by
    intros
    ring
  rw [e]
  apply mm_finset_sum
  intro m hm
  have hm' : m < n := Finset.mem_range.mp hm
  obtain ⟨q, hq⟩ := hpr.dvd_choose_self (Nat.succ_ne_zero m) (by omega)
  rw [hq, Nat.cast_mul]
  unfold VF.MM
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow,
    AddValuation.map_pow, hvl]
  have h1 : (0 : WithTop ℝ) ≤ (m + 1) • V.v y := nsmul_nonneg (by simpa [VF.Ge] using hy) _
  have h2 : (0 : WithTop ℝ) ≤ (n + 1 - (m + 1)) • V.v z := nsmul_nonneg (by simpa [VF.Ge] using hz) _
  have h3 := v_natCast_nonneg_vf V q
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  exact lt_of_lt_of_le (lt_of_lt_of_le h01 (le_add_of_nonneg_right h3)) (le_add_of_nonneg_left (add_nonneg h1 h2))

theorem mm_sum_pow {ι : Type} (s : Finset ι) (a : ι → C) (ha : ∀ i, V.Ge 0 (a i)) :
    V.MM ((∑ i ∈ s, a i) ^ V.l - ∑ i ∈ s, a i ^ V.l) := by
  classical
  refine Finset.induction_on s ?_ (fun x t hx ih => ?_)
  · simp only [Finset.sum_empty, sub_zero]
    rw [zero_pow V.l_prime.ne_zero]
    unfold VF.MM
    rw [AddValuation.map_zero, ← WithTop.coe_zero]
    exact WithTop.coe_lt_top _
  · rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hS : V.Ge 0 (∑ i ∈ t, a i) := by
      unfold VF.Ge
      apply AddValuation.map_le_sum
      intro i _
      exact ha i
    have e : (a x + ∑ i ∈ t, a i) ^ V.l - (a x ^ V.l + ∑ i ∈ t, a i ^ V.l) =
        ((a x + ∑ i ∈ t, a i) ^ V.l - a x ^ V.l - (∑ i ∈ t, a i) ^ V.l) +
          ((∑ i ∈ t, a i) ^ V.l - ∑ i ∈ t, a i ^ V.l) := by
      ring
    rw [e]
    exact mm_add_of_both (mm_add_pow_l_sub_pow_l_sub_pow_l (ha x) hS) ih

private theorem single_zero_apply_up_two_eq_zero (i : Fin dd) (L : ℕ) (t : Fin 2 × Fin dd) :
    (Finsupp.single ((0 : Fin 3), i) L : Fin 3 × Fin dd →₀ ℕ) (up 2 t) = 0 := by
  rw [Finsupp.single_apply, if_neg]
  intro h
  simp only [up, Prod.mk.injEq] at h
  exact Fin.succ_ne_zero _ h.1.symm

private theorem ix_apply_up_two (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (t : Fin 2 × Fin dd) :
    ix i L γ (up 2 t) = γ t := by
  rw [ix, Finsupp.add_apply, single_zero_apply_up_two_eq_zero, zero_add, Finsupp.mapDomain_apply (up_inj 2)]

theorem ix_div (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) (L : ℕ) (hL : 0 < L) :
    (ix i L γ).mapRange (fun n => n / L) (Nat.zero_div L) =
      (γ.mapRange (fun n => n / L) (Nat.zero_div L)).mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1 := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
    rw [Finsupp.mapRange_apply, index_raise_first, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, zero_add,
      Finsupp.single_apply]
    by_cases h : j = i
    · subst h
      simp [Nat.div_self hL]
    · simp [h, Ne.symm h]
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapRange_apply, ix_apply_up_two, Finsupp.add_apply, single_zero_apply_up_two_eq_zero, add_zero,
      Finsupp.mapDomain_apply (up_inj 2), Finsupp.mapRange_apply]

theorem ix_dvd (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    (∀ s, V.l ∣ ix i V.l γ s) ↔ ∀ t, V.l ∣ γ t := by
  constructor
  · intro h t
    have := h (up 2 t)
    rwa [ix_apply_up_two] at this
  · rintro h ⟨k, j⟩
    induction k using Fin.cases with
    | zero =>
      rw [index_raise_first]
      split_ifs <;> simp
    | succ k' =>
      have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
      rw [e, ix_apply_up_two]
      exact h _

theorem phiP (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (Y.B.ph2 ^ V.l) γ - coeff γ (frobTw V.l (Y.chartLinearTerm u))) := by
  have hl := V.l_prime
  have hP := MaximalIdealCongruence.mms_pow_frobTw (V := V) Y.intPh2
  have e1 : Phi V u (Y.B.ph2 ^ V.l) γ =
      ∑ i, u i ^ V.l * (coeff (ix i V.l γ) (Y.B.ph2 ^ V.l - frobTw V.l Y.B.ph2)) +
        ∑ i, u i ^ V.l * coeff (ix i V.l γ) (frobTw V.l Y.B.ph2) := by
    unfold Phi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub]; ring
  rw [e1, add_sub_assoc]
  refine GmExArith.mm_add (GmExArith.mm_sum fun i _ => GmExArith.mm_int_mul ((hu i).pow _) (hP _)) ?_
  rw [MaximalIdealCongruence.coeff_frobTw]
  by_cases hd : ∀ t, V.l ∣ γ t
  · rw [if_pos hd]
    have e2 : ∀ i, coeff (ix i V.l γ) (frobTw V.l Y.B.ph2) =
        (coeff ((γ.mapRange (fun n => n / V.l) (Nat.zero_div V.l)).mapDomain (up 2) +
          Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2) ^ V.l := by
      intro i
      rw [MaximalIdealCongruence.coeff_frobTw, if_pos ((ix_dvd i γ).2 hd), ix_div i γ V.l hl.pos]
    simp only [e2]
    set ν := γ.mapRange (fun n => n / V.l) (Nat.zero_div V.l) with hν
    have e3 : coeff ν (Y.chartLinearTerm u) = ∑ i, u i * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2 :=
      rfl
    rw [e3]
    have e4 : ∑ i, u i ^ V.l * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2 ^ V.l =
        ∑ i, (u i * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2) ^ V.l :=
      Finset.sum_congr rfl fun i _ => (mul_pow _ _ _).symm
    rw [e4, ← neg_sub]
    exact GmExArith.mm_neg (mm_sum_pow _ _ fun i => (hu i).mul_int (Y.intPh2 _))
  · rw [if_neg hd, sub_zero]
    refine GmExArith.mm_sum fun i _ => ?_
    rw [MaximalIdealCongruence.coeff_frobTw, if_neg (fun h => hd ((ix_dvd i γ).1 h)), mul_zero]
    exact GmExArith.mm_zero

end Formalism.L2.FormalSeriesBounds.FunEq
