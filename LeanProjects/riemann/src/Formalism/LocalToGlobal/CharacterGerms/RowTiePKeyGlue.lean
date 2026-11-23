import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

section Glue

variable {C : Type} [Field C] {V : VF C}

theorem tends_pow_zero {a : C} (ha : V.MM a) : Tends V (fun n => a ^ V.l ^ n) 0 := by
  unfold Tends VF.MM at *
  intro w
  by_cases ha0 : a = 0
  · refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [ha0, zero_pow (pow_pos V.l_prime.pos n).ne', sub_zero, AddValuation.map_zero]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff V.v).mpr ha0)
    have hr0 : 0 < r := by
      rw [← hr] at ha
      exact WithTop.coe_pos.mp ha
    refine ⟨⌈w / r⌉₊, fun n hn => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [zero_sub, AddValuation.map_neg, AddValuation.map_pow, ← hr, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ ((V.l ^ n : ℕ) : ℝ) := by
      first
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt n).le
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt).le
    have h2 : w / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (div_mul_cancel₀ w hr0.ne').ge.trans (mul_le_mul_of_nonneg_right (h2.trans h1) hr0.le)

variable [CharZero C] {O : Type} [CommRing O] {n d : ℕ}

theorem chi_kill (K : KeyData C V O n d) (w : Fin n → C) (hw : w ≠ 0) (hP : Matrix.mulVec K.P w = w)
    (χ : O →+* C) (hχ : ∀ x, Matrix.mulVec (K.ρ x) w = χ x • w) :
    (∀ y, V.Ge 0 (χ y)) ∧ ∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z) := by
  have hint : ∀ y, V.Ge 0 (χ y) := fun y => eig_int (K.ρ y) (K.ρ_int y) w hw (χ y) (hχ y)
  refine ⟨hint, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  have hT : Tends V (fun m => χ K.ε ^ V.l ^ m * w i) (w i) := by
    have h1 : Tends V (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) (Matrix.mulVec K.P w i) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Tends.sum _ fun j _ => Tends.mul ?_ (tends_const _)
      exact RowTiePProj.tends_of_nat fun N => K.P_lim N i j
    have e : (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) = fun m => χ K.ε ^ V.l ^ m * w i := by
      funext m
      rw [hχ, map_pow]; rfl
    rw [e, hP] at h1
    exact h1
  have hunit : ¬ V.MM (χ K.ε) := by
    intro hm
    have h0 := (tends_pow_zero hm).mul (tends_const (V := V) (w i))
    rw [zero_mul] at h0
    exact hi (hT.unique h0)
  intro z hz
  obtain ⟨y, hy⟩ := K.ε_ann z hz
  have h1 := congrArg (fun t => V.v (χ t)) hy
  simp only [map_mul, map_natCast, AddValuation.map_mul, V.v_l] at h1
  unfold VF.MM at hunit ⊢
  push_neg at hunit
  have he0 : V.v (χ K.ε) = 0 := le_antisymm hunit (hint K.ε)
  rw [he0, zero_add] at h1
  rw [h1]
  have := hint y
  unfold VF.Ge at this
  calc (0 : WithTop ℝ) < 1 := by exact_mod_cast one_pos
    _ = 1 + 0 := (add_zero _).symm
    _ ≤ 1 + V.v (χ y) := add_le_add le_rfl (by exact_mod_cast this)

end Glue

section Top

theorem keyLA_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) (C : Type) [Field C] [CharZero C] (V : VF C)
    (hac : IsAlgClosed C)
    (hcpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (x : O) :
    Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P = 0 := by
  have hv : ∀ v : Fin n → C,
      Matrix.mulVec (Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P) v = 0 := by
    intro v
    obtain ⟨m, w, χ, hPv, hw⟩ := hE C V hac hcpl O n d K v
    rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h0 : w j = 0
    · rw [h0, Matrix.mulVec_zero]
    obtain ⟨hPw, hχ⟩ := hw j
    obtain ⟨hint, hkill⟩ := chi_kill K (w j) h0 hPw (χ j) hχ
    obtain ⟨c, hc⟩ := hR C V O n d K (χ j) hint hkill
    have heq := hD C V O n d K (χ j) c hint hc
    rw [aeval_mulVec _ _ _ (hχ x), Polynomial.eval_prod]
    have : ∏ c' : ZMod d, Polynomial.eval (χ j x) (Polynomial.X - Polynomial.C (K.em c' x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self])
    rw [this, zero_smul]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem key_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) : KeySt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g ε hε hε1 hεx e he x
  let K : KeyData C V O dd d :=
    { ρ := linHom Y
      ρ_int := fun x i j => Y.intAct x i _
      P := linM e
      em := fun a => p.em g a
      em_int := fun a x => p.em_int g a x
      em_frob := fun a x => p.em_frob g a x
      ε := ε
      ε_idem := hε
      ε_one := hε1
      ε_ann := hεx
      P_lim := fun N i j => he N i _ }
  exact keyLA_of hE hR hD C V Y.algClosed Y.cpl O dd d K x

end Top

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
