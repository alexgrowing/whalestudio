import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.NormCut

section Asm

variable {I : Type*} [Group I] [Fintype I]

def gamOf (U : Set I) (p : I → ℂ) (x : I) : ℂ := ((Nat.card U : ℂ))⁻¹ * ∑ y : I, p (y * x * y⁻¹)

theorem gamOf_comm (U : Set I) (p : I → ℂ) (x y : I) : gamOf U p (x * y) = gamOf U p (y * x) := by
  unfold gamOf
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight y)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group

theorem pairSum_gam (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (i j : I) :
    ∑ s : I, ∑ s' : I, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) ^ 2 * conj (gamOf U p (i * j⁻¹)) := by
  have hU' : ∀ x : I, ∑ t : I, conj (p (x * t)) * p t = (Nat.card U : ℂ) * conj (p x) := by
    intro x
    have e : ∀ t, conj (p (x * t)) * p t = if t ∈ U then conj (p x) else 0 := by
      intro t
      split_ifs with ht
      · rw [hr x t ht, map_mul, mul_assoc, hn t ht, mul_one]
      · rw [h0 t ht, mul_zero]
    simp_rw [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have step : ∀ s : I, ∑ s' : I, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) * conj (p (s⁻¹ * (i * j⁻¹) * s)) := by
    intro s
    rw [← Equiv.sum_comp (Equiv.mulLeft (j⁻¹ * s)), ← hU' (s⁻¹ * (i * j⁻¹) * s)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [show s⁻¹ * i * (j⁻¹ * s * t) = s⁻¹ * (i * j⁻¹) * s * t by group,
      show s⁻¹ * j * (j⁻¹ * s * t) = t by group]
  simp_rw [step]
  rw [← Finset.mul_sum]
  have hsw : ∑ s : I, conj (p (s⁻¹ * (i * j⁻¹) * s)) = ∑ y : I, conj (p (y * (i * j⁻¹) * y⁻¹)) := by
    rw [← Equiv.sum_comp (Equiv.inv I)]
    simp
  rw [hsw]
  unfold gamOf
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  field_simp

private lemma orbit_lemma_2 {C : Type*} [Fintype C] (A U : Set I) (s : C → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I))) (g : I → ℂ)
    (hg : ∀ x, ∀ a ∈ A, ∀ w ∈ U, g (a * x * w) = g x) :
    ∑ x : I, g x = ((Nat.card A : ℂ) * (Nat.card U : ℂ)) * ∑ c : C, g (s c) := by
  rw [← hb.sum_comp]
  simp only [Fintype.sum_prod_type]
  have e : ∀ (a : A) (c : C) (u : U), g ((a : I) * s c * (u : I)) = g (s c) :=
    fun a c u => hg (s c) a a.2 u u.2
  simp only [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]
  ring

theorem orbitSum2 {C C' : Type*} [Fintype C] [Fintype C'] (A A' U : Set I) (s : C → I) (s' : C' → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I)))
    (hb' : Function.Bijective (fun x : A' × C' × U => (x.1 : I) * s' x.2.1 * (x.2.2 : I))) (f : I → I → ℂ)
    (hL : ∀ x y, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) y = f x y)
    (hR : ∀ x y, ∀ a ∈ A', ∀ w ∈ U, f x (a * y * w) = f x y) :
    ∑ x : I, ∑ y : I, f x y =
      ((Nat.card A : ℂ) * (Nat.card U : ℂ)) * ((Nat.card A' : ℂ) * (Nat.card U : ℂ)) *
        ∑ c : C, ∑ c' : C', f (s c) (s' c') := by
  rw [orbit_lemma_2 A U s hb (fun x => ∑ y, f x y)
    (fun x a ha w hw => Finset.sum_congr rfl fun y _ => hL x y a ha w hw)]
  have e : ∀ c, ∑ y, f (s c) y = ((Nat.card A' : ℂ) * (Nat.card U : ℂ)) * ∑ c', f (s c) (s' c') :=
    fun c => orbit_lemma_2 A' U s' hb' (f (s c)) (fun y a ha w hw => hR (s c) y a ha w hw)
  simp_rw [e, ← Finset.mul_sum]
  ring

theorem inner_sum_smul {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (c : I → ℂ) (Z : I → K) :
    inner ℂ (∑ i, c i • Z i) (∑ j, c j • Z j) = ∑ i, ∑ j, conj (c i) * c j * inner ℂ (Z i) (Z j) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]
  ring

def Zs {τ K Q : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (S : Set τ) (intersection_update_fsHerm_neg_one : τ → Q) (ιt : τ → I)
    (a : τ → K) (q : Q) (i : I) : K :=
  ∑' t, if t ∈ S ∧ intersection_update_fsHerm_neg_one t = q ∧ ιt t = i then a t else 0

end Asm

section Inv

variable {I : Type*} [Group I] [Fintype I]

def fForm (p : I → ℂ) (Gm : I → I → ℂ) (x y : I) : ℂ :=
  ∑ i, ∑ j, conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j

theorem fForm_left (U : Set I) (p : I → ℂ) (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (b * i) (b * j) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm (b * x * w) y = fForm p Gm x y := by
  have hq : ∀ m, p (w⁻¹ * m) = conj (p w) * p m := by
    intro m
    have e := hl (w⁻¹ * m) w hw
    rw [mul_inv_cancel_left] at e
    rw [e, ← mul_assoc, hn w hw, one_mul]
  unfold fForm
  rw [← Equiv.sum_comp (Equiv.mulLeft b)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft b)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_mulLeft, hG]
  rw [show (b * x * w)⁻¹ * (b * i) * y = w⁻¹ * (x⁻¹ * i * y) by group,
    show (b * x * w)⁻¹ * (b * j) * y = w⁻¹ * (x⁻¹ * j * y) by group, hq, hq, map_mul, Complex.conj_conj]
  linear_combination (conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j) * hn w hw

theorem fForm_right (U : Set I) (p : I → ℂ) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (i * b⁻¹) (j * b⁻¹) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm x (b * y * w) = fForm p Gm x y := by
  unfold fForm
  rw [← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_mulRight, hG]
  rw [show x⁻¹ * (i * b⁻¹) * (b * y * w) = x⁻¹ * i * y * w by group,
    show x⁻¹ * (j * b⁻¹) * (b * y * w) = x⁻¹ * j * y * w by group, hr _ w hw, hr _ w hw, map_mul]
  linear_combination (conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j) * hn w hw

theorem fForm_sum (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (Gm : I → I → ℂ) :
    ∑ x : I, ∑ y : I, fForm p Gm x y =
      (Nat.card U : ℂ) ^ 2 * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * Gm i j := by
  have hswap : ∀ (F : I → I → I → I → ℂ),
      ∑ x, ∑ y, ∑ i, ∑ j, F x y i j = ∑ i, ∑ j, ∑ x, ∑ y, F x y i j := by
    intro F
    calc ∑ x, ∑ y, ∑ i, ∑ j, F x y i j = ∑ x, ∑ i, ∑ j, ∑ y, F x y i j := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ x, ∑ y, F x y i j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
  unfold fForm
  refine (hswap (fun x y i j => conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j)).trans ?_
  simp_rw [← Finset.sum_mul]
  simp_rw [pairSum_gam U p h0 hr hn hU]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Inv

section Main

variable {I : Type} [Group I] [Fintype I]

theorem card_ne_zero_of_bij {C : Type*} (A U : Set I) (s : C → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I))) :
    (Nat.card A : ℂ) ≠ 0 ∧ (Nat.card U : ℂ) ≠ 0 := by
  obtain ⟨⟨a, c, u⟩, -⟩ := hb.2 1
  haveI : Nonempty A := ⟨a⟩
  haveI : Nonempty U := ⟨u⟩
  exact ⟨by exact_mod_cast (Nat.card_pos (α := A)).ne', by exact_mod_cast (Nat.card_pos (α := U)).ne'⟩

set_option maxHeartbeats 800000 in

theorem normExp_abs {τ Rw H K Q1 Q2 R R' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype Q1] [Fintype Q2] [Fintype R]
    [Fintype R'] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H (PiLp 2 (fun _ : Q1 × Q2 => K))) (S : Set τ)
    (lamR : R → Q1) (lamR' : R' → Q2) (Bl : R → R' → H →L[ℂ] K)
    (hBl : ∀ x y : H, inner ℂ x y = ∑ ρ, ∑ ρ', inner ℂ (Bl ρ ρ' x) (Bl ρ ρ' y))
    (intersection_update_fsHerm_neg_one : τ → Q1 × Q2) (a : τ → K) (ιt : τ → I) (p : I → ℂ) (sR : R → I) (sR' : R' → I)
    (hop : ∀ t ρ ρ', Bl ρ ρ' (X.op t) =
      if intersection_update_fsHerm_neg_one t = (lamR ρ, lamR' ρ') then p ((sR ρ)⁻¹ * ιt t * sR' ρ') • a t else 0)
    (w : Q1 × Q2 → ℝ) (hw0 : ∀ q, 0 < w q)
    (hvec : ∀ t, X.vec t = WithLp.toLp 2 (fun q => if q = intersection_update_fsHerm_neg_one t then ((w q : ℝ) : ℂ) • a t else 0))
    (hio : ∀ t, X.io (X.rowOf t) = ιt t)
    (U : Set I) (h0 : ∀ x, x ∉ U → p x = 0) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x) (hn : ∀ u ∈ U, conj (p u) * p u = 1)
    (hGG : ∀ i j, X.GG i j = conj (gamOf U p (j⁻¹ * i)))
    (A : Q1 → Set I) (A' : Q2 → Set I)
    (hA : ∀ q, Function.Bijective
      (fun x : A q × {ρ // lamR ρ = q} × U => (x.1 : I) * sR x.2.1.1 * (x.2.2 : I)))
    (hA' : ∀ q, Function.Bijective
      (fun x : A' q × {ρ // lamR' ρ = q} × U => (x.1 : I) * sR' x.2.1.1 * (x.2.2 : I)))
    (hwA : ∀ q, w q ^ 2 = ((Nat.card (A q.1) : ℝ) * (Nat.card (A' q.2) : ℝ))⁻¹)
    (hsatL : ∀ q, ∀ b ∈ A q.1, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (b * i)) (Zs S intersection_update_fsHerm_neg_one ιt a q (b * j)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsatR : ∀ q, ∀ b ∈ A' q.2, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (i * b⁻¹)) (Zs S intersection_update_fsHerm_neg_one ιt a q (j * b⁻¹)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsum : Summable fun t => ‖X.op t‖) (hsumv : Summable fun t => ‖X.vec t‖) :
    X.NormExpansionOn S := by
  classical
  set G : Q1 × Q2 → I → I → ℂ := fun q i j => inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j) with hGdef

  have ha_le : ∀ t, w (intersection_update_fsHerm_neg_one t) * ‖a t‖ ≤ ‖X.vec t‖ := by
    intro t
    have e : (X.vec t).ofLp (intersection_update_fsHerm_neg_one t) = ((w (intersection_update_fsHerm_neg_one t) : ℝ) : ℂ) • a t := by
      rw [hvec t, PiLp.toLp_apply, if_pos rfl]
    have h1 := PiLp.norm_apply_le (X.vec t) (intersection_update_fsHerm_neg_one t)
    rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw0 _).le] at h1
    exact h1
  have hsm : ∀ (q : Q1 × Q2) (c : τ → Prop) {dc : DecidablePred c} (z : ℂ), (∀ t, c t → intersection_update_fsHerm_neg_one t = q) →
      Summable (fun t => if c t then z • a t else 0) := by
    intro q c dc z hc
    refine Summable.of_norm_bounded (g := fun t => ‖z‖ * ((w q)⁻¹ * ‖X.vec t‖))
      ((hsumv.mul_left _).mul_left _) ?_
    intro t
    by_cases h : c t
    · rw [if_pos h, norm_smul]
      gcongr
      have := ha_le t
      rw [hc t h] at this
      rw [inv_mul_eq_div, le_div_iff₀ (hw0 q)]
      linarith
    · rw [if_neg h, norm_zero]
      have := hw0 q
      positivity

  have hF : Summable (S.indicator X.op) := (hsum.of_norm).indicator S
  have hBl_part : ∀ ρ ρ', Bl ρ ρ' (X.part S) =
      ∑ i, p ((sR ρ)⁻¹ * i * sR' ρ') • Zs S intersection_update_fsHerm_neg_one ιt a (lamR ρ, lamR' ρ') i := by
    intro ρ ρ'
    unfold Formalism.FourierDecayAlt.PB.Terms.part Zs
    rw [(Bl ρ ρ').map_tsum hF]
    simp_rw [← tsum_const_smul'', smul_ite, smul_zero]
    rw [← Summable.tsum_finsetSum]
    swap
    · intro i _
      exact hsm (lamR ρ, lamR' ρ') _ _ (fun t h => h.2.1)
    refine tsum_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [if_pos ht, hop t ρ ρ']
      by_cases hs : intersection_update_fsHerm_neg_one t = (lamR ρ, lamR' ρ')
      · rw [if_pos hs, Finset.sum_eq_single (ιt t)]
        · rw [if_pos ⟨ht, hs, rfl⟩]
        · intro i _ hi
          exact if_neg (fun h => hi h.2.2.symm)
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun h => hs h.2.1)
    · rw [if_neg ht, map_zero]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => ht h.1)
  have hnorm : ‖X.part S‖ ^ 2 = (∑ ρ, ∑ ρ', fForm p (G (lamR ρ, lamR' ρ')) (sR ρ) (sR' ρ')).re := by
    rw [@norm_sq_eq_re_inner ℂ, hBl]
    simp only [hBl_part, inner_sum_smul, fForm, hGdef]
    rfl

  have hfib : ∀ q1 q2, ∑ ρ : {ρ // lamR ρ = q1}, ∑ ρ' : {ρ' // lamR' ρ' = q2},
      fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) =
        (((w (q1, q2)) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G (q1, q2) i j := by
    intro q1 q2
    have hrw : ∀ (ρ : {ρ // lamR ρ = q1}) (ρ' : {ρ' // lamR' ρ' = q2}),
        fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) = fForm p (G (q1, q2)) (sR ρ.1) (sR' ρ'.1) := by
      intro ρ ρ'; rw [ρ.2, ρ'.2]
    simp_rw [hrw]
    have hc := card_ne_zero_of_bij (A q1) U (fun c : {ρ // lamR ρ = q1} => sR c.1) (hA q1)
    have hc' := card_ne_zero_of_bij (A' q2) U (fun c : {ρ' // lamR' ρ' = q2} => sR' c.1) (hA' q2)
    have ho := orbitSum2 (A q1) (A' q2) U (fun c : {ρ // lamR ρ = q1} => sR c.1)
      (fun c : {ρ' // lamR' ρ' = q2} => sR' c.1) (hA q1) (hA' q2) (fForm p (G (q1, q2)))
      (fun x y b hb v hv => fForm_left U p hl hn _ b (fun i j => hsatL (q1, q2) b hb i j) x y v hv)
      (fun x y b hb v hv => fForm_right U p hr hn _ b (fun i j => hsatR (q1, q2) b hb i j) x y v hv)
    rw [fForm_sum U p h0 hr hn hc.2] at ho
    try beta_reduce at ho
    have hne : ((Nat.card (A q1) : ℂ) * Nat.card U) * ((Nat.card (A' q2) : ℂ) * Nat.card U) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc.1 hc.2) (mul_ne_zero hc'.1 hc'.2)
    have hw2 : (((w (q1, q2)) ^ 2 : ℝ) : ℂ) = ((Nat.card (A q1) : ℂ) * (Nat.card (A' q2) : ℂ))⁻¹ := by
      rw [hwA]; push_cast; ring
    obtain ⟨hA1, hU1⟩ := hc
    obtain ⟨hA2, -⟩ := hc'
    rw [hw2]
    apply mul_left_cancel₀ hne
    rw [← ho]
    field_simp

  have hvp : ∀ i q, (X.vecPart S i).ofLp q = ((w q : ℝ) : ℂ) • Zs S intersection_update_fsHerm_neg_one ιt a q i := by
    intro i q
    unfold Formalism.FourierDecayAlt.PB.Terms.vecPart Zs
    have hs : Summable ((S ∩ {t | X.io (X.rowOf t) = i}).indicator X.vec) := (hsumv.of_norm).indicator _
    have hm := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Q1 × Q2 => K) q).map_tsum hs
    simp only [PiLp.proj_apply] at hm
    rw [hm, ← tsum_const_smul'']
    refine tsum_congr fun t => ?_
    by_cases h1 : t ∈ S <;> by_cases h2 : ιt t = i <;> by_cases h3 : intersection_update_fsHerm_neg_one t = q <;>
      simp [Set.indicator_apply, hvec t, hio t, h1, h2, h3, @eq_comm _ q (intersection_update_fsHerm_neg_one t)]
  have hinner : ∀ i j, inner ℂ (X.vecPart S i) (X.vecPart S j) = ∑ q, (((w q) ^ 2 : ℝ) : ℂ) * G q i j := by
    intro i j
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hvp, hvp, inner_smul_left, inner_smul_right, Complex.conj_ofReal, hGdef]
    push_cast
    ring
  unfold Formalism.FourierDecayAlt.PB.Terms.NormExpansionOn
  rw [hnorm]
  congr 1
  simp_rw [hinner, hGG]
  calc ∑ ρ, ∑ ρ', fForm p (G (lamR ρ, lamR' ρ')) (sR ρ) (sR' ρ')
      = ∑ q1, ∑ ρ : {ρ // lamR ρ = q1}, ∑ q2, ∑ ρ' : {ρ' // lamR' ρ' = q2},
          fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) := by
        rw [← Fintype.sum_fiberwise lamR]
        refine Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun ρ _ => ?_
        exact (Fintype.sum_fiberwise lamR' _).symm
    _ = ∑ q1, ∑ q2, ∑ ρ : {ρ // lamR ρ = q1}, ∑ ρ' : {ρ' // lamR' ρ' = q2},
          fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) := by
        refine Finset.sum_congr rfl fun q1 _ => ?_
        exact Finset.sum_comm
    _ = ∑ q1, ∑ q2, (((w (q1, q2)) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G (q1, q2) i j := by
        refine Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun q2 _ => hfib q1 q2
    _ = ∑ q : Q1 × Q2, (((w q) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G q i j :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, conj (gamOf U p (j⁻¹ * i)) * ∑ q, (((w q) ^ 2 : ℝ) : ℂ) * G q i j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
        rw [gamOf_comm U p i j⁻¹]
        ring

end Main

end Formalism.L2.SG.NormCut
