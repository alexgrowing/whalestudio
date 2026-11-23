import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriFactorization

open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.TwContraction

section Algebra

variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}

def Dp (ρ : ValueGroupWithZero F) (j : ℕ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i l, valuation F (M i l) ≤ ρ ^ j

theorem Dp.mul {ρ : ValueGroupWithZero F} {a b : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : Dp ρ a M) (hN : Dp ρ b N) : Dp ρ (a + b) (M * N) := by
  intro i l
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun r _ => ?_
  rw [map_mul, pow_add]
  exact mul_le_mul' (hM i r) (hN r l)

theorem Dp.add {ρ : ValueGroupWithZero F} {a : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : Dp ρ a M) (hN : Dp ρ a N) : Dp ρ a (M + N) := fun i l =>
  (Valuation.map_add _ _ _).trans (max_le (hM i l) (hN i l))

theorem Dp.mono {ρ : ValueGroupWithZero F} (hρ : ρ ≤ 1) {a b : ℕ} (hab : a ≤ b)
    {M : Matrix (Fin n) (Fin n) F} (hM : Dp ρ b M) : Dp ρ a M := fun i l =>
  (hM i l).trans (pow_le_pow_right_of_le_one' hρ hab)

theorem perm_eq_one_of_le (π : Equiv.Perm (Fin n)) (h : ∀ i, π i ≤ i) : π = 1 := by
  have key : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) = m → π i = i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      refine le_antisymm (h i) ?_
      by_contra hlt
      have hlt' : π i < i := not_le.mp hlt
      have h2 : π (π i) = π i := ih (π i) (by rw [← hi]; exact hlt') _ rfl
      exact hlt'.ne (π.injective h2)
  exact Equiv.ext fun i => key i i rfl

theorem val_det_sub_prod_lt (M : Matrix (Fin n) (Fin n) F)
    (h0 : ∀ i l, valuation F (M i l) ≤ 1) (hl : ∀ i l, l < i → valuation F (M i l) < 1) :
    valuation F (M.det - ∏ i, M i i) < 1 := by
  classical
  rw [Matrix.det_apply', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, Equiv.Perm.coe_one, id_eq, one_mul]
  rw [add_sub_cancel_left]
  refine Valuation.map_sum_lt _ one_ne_zero fun π hπ => ?_
  have hπ1 : π ≠ 1 := (Finset.mem_erase.mp hπ).1
  obtain ⟨i, hi⟩ : ∃ i, i < π i := by
    by_contra hcon
    exact hπ1 (perm_eq_one_of_le π fun i => not_lt.mp fun h => hcon ⟨i, h⟩)
  have hs : valuation F (((Equiv.Perm.sign π : ℤˣ) : ℤ) : F) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [map_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]
  have hrest : valuation F (∏ r ∈ Finset.univ.erase i, M (π r) r) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun r _ => h0 _ _
  calc _ ≤ 1 * (valuation F (M (π i) i) * 1) := mul_le_mul' hs (mul_le_mul' le_rfl hrest)
    _ < 1 := by simpa using hl _ _ hi

theorem mem_unitGL_entries {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) (i l : Fin n) :
    valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1 := by
  obtain ⟨g₀, rfl⟩ := hg
  exact ((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))) i l).2

theorem val_det_of_mem_unitGL {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) :
    valuation F (g : Matrix (Fin n) (Fin n) F).det = 1 := by
  obtain ⟨g₀, rfl⟩ := hg
  have hdet : ∀ h : GL (Fin n) (Valuation.integer (valuation F)),
      ((Matrix.GeneralLinearGroup.map (Valuation.integer (valuation F)).subtype h : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).det =
        (((h : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det :
          Valuation.integer (valuation F)) : F) := fun h =>
    ((Valuation.integer (valuation F)).subtype.map_det _).symm
  rw [hdet]
  have h1 : valuation F (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) ≤ 1 :=
    ((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det).2
  have h2 : valuation F ((((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) ≤ 1 :=
    (((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det).2
  have h3 : (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) *
      ((((g₀⁻¹ : GL (Fin n) (Valuation.integer (valuation F))) : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp
  have h4 := congrArg (valuation F) h3
  rw [map_mul, map_one] at h4
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero F) = _ := h4.symm
    _ ≤ valuation F (((g₀ : Matrix (Fin n) (Fin n) (Valuation.integer (valuation F))).det : Valuation.integer (valuation F)) : F) * 1 :=
        mul_le_mul' le_rfl h2
    _ = _ := mul_one _

theorem mem_unitGL_of (g : GL (Fin n) F) (h0 : ∀ i l, valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1)
    (hd : valuation F (g : Matrix (Fin n) (Fin n) F).det = 1) : g ∈ unitGL (n := Fin n) F := by
  set O := Valuation.integer (valuation F) with hO
  let M₀ : Matrix (Fin n) (Fin n) O := fun i l => ⟨(g : Matrix (Fin n) (Fin n) F) i l, h0 i l⟩
  have hmap : O.subtype.mapMatrix M₀ = (g : Matrix (Fin n) (Fin n) F) := by
    ext i l; rfl
  have hdet : ((M₀.det : O) : F) = (g : Matrix (Fin n) (Fin n) F).det := by
    have := O.subtype.map_det M₀
    rw [hmap] at this
    exact this
  have hne : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : valuation F ((g : Matrix (Fin n) (Fin n) F).det)⁻¹ ≤ 1 := by
    rw [map_inv₀, hd, inv_one]
  have hu : IsUnit M₀.det := by
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) ?_
    apply Subtype.ext
    show ((M₀.det : O) : F) * ((g : Matrix (Fin n) (Fin n) F).det)⁻¹ = 1
    rw [hdet, mul_inv_cancel₀ hne]
  refine ⟨Matrix.GeneralLinearGroup.mk'' M₀ hu, Units.ext ?_⟩
  ext i l
  rfl

theorem val_diag_of_mem_iwahori {c : GL (Fin n) F} (hc : c ∈ iwahori (m := n) F) (i : Fin n) :
    valuation F ((c : Matrix (Fin n) (Fin n) F) i i) = 1 := by
  have h1 := val_det_sub_prod_lt (c : Matrix (Fin n) (Fin n) F) (mem_unitGL_entries hc.1) hc.2
  have hd := val_det_of_mem_unitGL hc.1
  have h2 : valuation F (∏ i, (c : Matrix (Fin n) (Fin n) F) i i) = 1 := by
    rw [← hd]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd, Valuation.map_sub_swap]
    exact h1
  rw [map_prod] at h2
  exact (Finset.prod_eq_one_iff_of_le_one' fun r _ => mem_unitGL_entries hc.1 r r).1 h2 i (Finset.mem_univ i)

end Algebra

section Step

variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}

theorem step (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = iwahori (m := n) F)
    (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a)
    (hτU : ∀ g ∈ U, Matrix.GeneralLinearGroup.map (τ : F →+* F) g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (j : ℕ) (c : GL (Fin n) F) (hcU : c ∈ U)
    (hcD : ∀ i l, i ≠ l → valuation F ((c : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j) :
    ∃ p ∈ U, x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p ∈ U ∧
      ∀ i l, i ≠ l → valuation F (((x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ (j + 1) := by
  have hI : c ∈ iwahori (m := n) F := by rw [← hU]; exact hcU
  have hρ1' : ρ ≤ 1 := hρ1.le
  set C : Matrix (Fin n) (Fin n) F := (c : Matrix (Fin n) (Fin n) F) with hCdef
  let d : Fin n → F := fun i => C i i
  have hd : ∀ i, valuation F (d i) = 1 := fun i => val_diag_of_mem_iwahori hI i
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hτs : ∀ a, valuation F (τ.symm a) = valuation F a := fun a => by
    have := hτ (τ.symm a)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hev : ∀ i, valuation F (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).2 (he i)
  have hq : ∀ i l, i < l → valuation F (e i / e l) ≤ ρ := fun i l h => by
    rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 (hev l))]
    exact hc i l h
  set s : ℕ := max j 1 with hs
  have hs1 : 1 ≤ s := le_max_right _ _
  have hjs : j ≤ s := le_max_left _ _
  have hsj : s ≤ j + 1 := max_le (Nat.le_succ j) (Nat.le_add_left 1 j)
  have hlow : ∀ i l, l < i → valuation F (C i l) ≤ ρ ^ s := fun i l h => by
    rcases max_choice j 1 with h' | h'
    · rw [hs, h']; exact hcD i l h.ne'
    · rw [hs, h', pow_one]; exact hunif _ (hI.2 i l h)
  let T : Matrix (Fin n) (Fin n) F := fun i l =>
    if l < i then - τ.symm (C i l / d i) else if i < l then (e i / e l) * (C i l / d l) else 0
  have hTlo : ∀ i l, l < i → T i l = - τ.symm (C i l / d i) := fun i l h => if_pos h
  have hTup : ∀ i l, i < l → T i l = (e i / e l) * (C i l / d l) := fun i l h => by
    show (if l < i then _ else _) = _
    rw [if_neg (not_lt.2 h.le), if_pos h]
  have hTd : ∀ i, T i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hTlov : ∀ i l, l < i → valuation F (T i l) ≤ ρ ^ s := fun i l h => by
    rw [hTlo i l h, Valuation.map_neg, hτs, map_div₀, hd, div_one]
    exact hlow i l h
  have hTupv : ∀ i l, i < l → valuation F (T i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hTup i l h, map_mul, map_div₀ _ (C i l), hd, div_one, pow_succ']
    exact mul_le_mul' (hq i l h) (hcD i l h.ne)
  have hT : Dp ρ s T := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · exact (hTupv i l h).trans (pow_le_pow_right_of_le_one' hρ1' hsj)
    · subst h; rw [hTd, map_zero]; exact zero_le'
    · exact hTlov i l h
  have hρs : ρ ^ s ≤ ρ := by
    calc ρ ^ s ≤ ρ ^ 1 := pow_le_pow_right_of_le_one' hρ1' hs1
      _ = ρ := pow_one ρ
  set P : Matrix (Fin n) (Fin n) F := 1 + T with hP
  have hPd : ∀ i, P i i = 1 := fun i => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_eq, hTd, add_zero]
  have hPo : ∀ i l, i ≠ l → P i l = T i l := fun i l h => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_ne h, zero_add]
  have hPint : ∀ i l, valuation F (P i l) ≤ 1 := fun i l => by
    by_cases h : i = l
    · subst h; rw [hPd, map_one]
    · rw [hPo i l h]; exact (hT i l).trans (hρs.trans hρ1')
  have hPlow : ∀ i l, l < i → valuation F (P i l) < 1 := fun i l h => by
    rw [hPo i l h.ne']
    exact lt_of_le_of_lt ((hT i l).trans hρs) hρ1
  have hPdet : valuation F P.det = 1 := by
    have h1 := val_det_sub_prod_lt P hPint hPlow
    rw [Finset.prod_congr rfl fun i _ => hPd i, Finset.prod_const_one] at h1
    have := Valuation.map_eq_of_sub_lt (valuation F) (x := (1 : F)) (y := P.det) (by rwa [map_one])
    rwa [map_one] at this
  have hPne : P.det ≠ 0 := fun h => by
    rw [h, map_zero] at hPdet
    exact zero_ne_one hPdet
  let p : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPne
  have hpv : (p : Matrix (Fin n) (Fin n) F) = P := rfl
  have hpU : p ∈ U := by
    have : p ∈ iwahori (m := n) F := ⟨mem_unitGL_of p hPint hPdet, hPlow⟩
    rw [← hU] at this
    exact this
  have hxinv : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (e i)⁻¹ := by
    rw [Matrix.coe_units_inv, hx]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he i)
  let q : GL (Fin n) F := x⁻¹ * p * x
  set Q : Matrix (Fin n) (Fin n) F := (q : Matrix (Fin n) (Fin n) F) with hQdef
  have hQ : ∀ i l, Q i l = (e i)⁻¹ * P i l * e l := fun i l => by
    show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l = _
    rw [Units.val_mul, Units.val_mul, hxinv, hx, hpv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hQd : ∀ i, Q i i = 1 := fun i => by
    rw [hQ, hPd, mul_one, inv_mul_cancel₀ (he i)]
  have hQup : ∀ i l, i < l → Q i l = C i l / d l := fun i l h => by
    rw [hQ, hPo i l h.ne, hTup i l h]
    have h1 := he i
    have h2 := he l
    field_simp
  have hQlow : ∀ i l, l < i → valuation F (Q i l) ≤ ρ * ρ ^ s := fun i l h => by
    rw [hQ, hPo i l h.ne', show (e i)⁻¹ * T i l * e l = (e l / e i) * T i l by
      rw [div_eq_mul_inv]; ring, map_mul]
    exact mul_le_mul' (hq l i h) (hTlov i l h)
  have hQint : ∀ i l, valuation F (Q i l) ≤ 1 := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, map_div₀, hd, div_one]
      exact mem_unitGL_entries hI.1 i l
    · subst h; rw [hQd, map_one]
    · refine (hQlow i l h).trans ?_
      calc ρ * ρ ^ s ≤ 1 * 1 := mul_le_mul' hρ1' (hρs.trans hρ1')
        _ = 1 := one_mul 1
  have hQdet : valuation F Q.det = 1 := by
    have : Q.det = P.det := by
      show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = _
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hpv]
      have h3 : (x : Matrix (Fin n) (Fin n) F).det * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
        simp
      calc _ = P.det * ((x : Matrix (Fin n) (Fin n) F).det *
            ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) := by ring
        _ = P.det := by rw [h3, mul_one]
    rw [this]; exact hPdet
  have hqU : q ∈ U := by
    have : q ∈ iwahori (m := n) F := ⟨mem_unitGL_of q hQint hQdet, fun i l h =>
      lt_of_le_of_lt (hQlow i l h) (lt_of_le_of_lt (mul_le_mul' le_rfl hρs) (by
        calc ρ * ρ ≤ ρ * 1 := mul_le_mul' le_rfl hρ1'
          _ = ρ := mul_one ρ
          _ < 1 := hρ1 |>.trans_le le_rfl))⟩
    rw [← hU] at this
    exact this
  let T' : Matrix (Fin n) (Fin n) F := T.map τ
  have hT' : Dp ρ s T' := fun i l => by
    show valuation F (τ (T i l)) ≤ _
    rw [hτ]; exact hT i l
  let Dg : Matrix (Fin n) (Fin n) F := Matrix.diagonal d
  let Co : Matrix (Fin n) (Fin n) F := C - Dg
  have hCo : Dp ρ j Co := fun i l => by
    by_cases h : i = l
    · subst h
      show valuation F (C i i - Dg i i) ≤ _
      rw [show Dg i i = C i i from Matrix.diagonal_apply_eq _ _, sub_self, map_zero]
      exact zero_le'
    · show valuation F (C i l - Dg i l) ≤ _
      rw [show Dg i l = 0 from Matrix.diagonal_apply_ne _ h, sub_zero]
      exact hcD i l h
  let B : Matrix (Fin n) (Fin n) F := C + Dg * T' - Q * Dg
  have hBe : ∀ i l, B i l = C i l + d i * τ (T i l) - Q i l * d l := fun i l => by
    show (C + Dg * T' - Q * Dg) i l = _
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rfl
  have hB : Dp ρ (j + 1) B := fun i l => by
    rw [hBe]
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, div_mul_cancel₀ _ (hd0 l), add_sub_cancel_left, map_mul, hd, one_mul, hτ]
      exact hTupv i l h
    · subst h
      rw [hTd, hQd, map_zero, mul_zero, add_zero, one_mul]
      show valuation F (C i i - C i i) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · rw [hTlo i l h, map_neg, RingEquiv.apply_symm_apply, mul_neg, mul_div_cancel₀ _ (hd0 i),
        add_neg_cancel, zero_sub, Valuation.map_neg, map_mul, hd, mul_one]
      refine (hQlow i l h).trans ?_
      rw [← pow_succ']
      exact pow_le_pow_right_of_le_one' hρ1' (Nat.succ_le_succ hjs)
  let R : Matrix (Fin n) (Fin n) F := B + Co * T'
  have hR : Dp ρ (j + 1) R :=
    hB.add ((hCo.mul hT').mono hρ1' (Nat.add_le_add_left hs1 j))
  have hPτ : P.map τ = 1 + T' := by
    rw [hP, Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hid : C * P.map τ = Q * Dg + R := by
    rw [hPτ]
    show C * (1 + T') = Q * Dg + (C + Dg * T' - Q * Dg + (C - Dg) * T')
    noncomm_ring
  have hw : x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p =
      q⁻¹ * (c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p) := by
    show _ = (x⁻¹ * p * x)⁻¹ * _
    group
  refine ⟨p, hpU, ?_, ?_⟩
  · rw [hw]
    exact U.mul_mem (U.inv_mem hqU) (U.mul_mem hcU (hτU p hpU))
  · intro i l hil
    rw [hw]
    have hval : ((q⁻¹ * (c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = Dg + ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R := by
      rw [Units.val_mul, Units.val_mul]
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C * P.map τ) = _
      rw [hid, mul_add, ← mul_assoc]
      congr 1
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F) * Dg = Dg
      rw [← Units.val_mul, inv_mul_cancel]
      simp
    rw [hval, Matrix.add_apply, show Dg i l = 0 from Matrix.diagonal_apply_ne _ hil, zero_add]
    have hq0 : Dp ρ 0 ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [pow_zero]
      have : q⁻¹ ∈ iwahori (m := n) F := by
        rw [← hU]; exact U.inv_mem hqU
      exact mem_unitGL_entries this.1 a b
    have := (hq0.mul hR) i l
    rwa [zero_add] at this

end Step

section Main

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem continuous_of_val (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a) :
    Continuous τ := by
  refine continuous_of_continuousAt_zero τ ?_
  rw [ContinuousAt, map_zero,
    (IsValuativeTopology.hasBasis_nhds_zero' F).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero' F)]
  intro γ hγ
  exact ⟨γ, hγ, fun y hy => by simpa [hτ] using hy⟩

theorem continuous_map_gl (φ : F →+* F) (hφ : Continuous φ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ :
      Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F).map φ)
  · have : (fun g : GL (Fin n) F =>
        (((Matrix.GeneralLinearGroup.map φ g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
        fun g => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ := by
      funext g; rw [← map_inv]; rfl
    exact this ▸ (Units.continuous_coe_inv.matrix_map hφ)

theorem contraction (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = iwahori (m := n) F)
    (hcpt : IsCompact (iwahori (m := n) F))
    (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a)
    (hτU : ∀ g ∈ U, Matrix.GeneralLinearGroup.map (τ : F →+* F) g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (δ : GL (Fin n) F) (hδ : δ ∈ iwDouble F x) :
    ∃ m ∈ iwahori (m := n) F, ∃ t ∈ torusO F,
      m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m = x * t := by
  have hUI : ∀ g, g ∈ U ↔ g ∈ iwahori (m := n) F := fun g => by
    rw [← hU]; rfl
  let f : GL (Fin n) F → GL (Fin n) F := fun m =>
    x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m
  have hf : Continuous f :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul
      (continuous_map_gl _ (continuous_of_val τ hτ))
  let S : ℕ → Set (GL (Fin n) F) := fun j =>
    {m | m ∈ iwahori (m := n) F ∧ f m ∈ iwahori (m := n) F ∧
      ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}
  have hclosedI : IsClosed (iwahori (m := n) F) := hcpt.isClosed
  have hSc : ∀ j, IsClosed (S j) := fun j => by
    have h1 : IsClosed {m : GL (Fin n) F | ∀ i l, i ≠ l →
        valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun l => isClosed_iInter fun _ => ?_
      have hcont : Continuous fun m : GL (Fin n) F => (f m : Matrix (Fin n) (Fin n) F) i l :=
        (Units.continuous_val.comp hf).matrix_elem i l
      exact (IsNonarchimedeanLocalField.isCompact_closedBall F (ρ ^ j)).isClosed.preimage hcont
    exact hclosedI.inter ((hclosedI.preimage hf).inter h1)
  have hSn : ∀ j, (S j).Nonempty := by
    intro j
    induction j with
    | zero =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hδ
      have hfa : f a = b * Matrix.GeneralLinearGroup.map (τ : F →+* F) a := by
        show x⁻¹ * a⁻¹ * (a * x * b) * _ = _
        group
      have hfaI : f a ∈ iwahori (m := n) F := by
        rw [hfa, ← hUI]
        exact U.mul_mem ((hUI _).2 hb) (hτU _ ((hUI _).2 ha))
      refine ⟨a, ha, hfaI, fun i l _ => ?_⟩
      rw [pow_zero]
      exact mem_unitGL_entries hfaI.1 i l
    | succ j ih =>
      obtain ⟨m, hm, hfm, hD⟩ := ih
      obtain ⟨p, hp, hcU, hcD⟩ := step U hU τ hτ hτU ρ hρ1 hunif e he hc x hx j (f m)
        ((hUI _).2 hfm) hD
      have hfmp : f (m * p) = x⁻¹ * p⁻¹ * x * f m * Matrix.GeneralLinearGroup.map (τ : F →+* F) p := by
        show x⁻¹ * (m * p)⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) (m * p) =
          x⁻¹ * p⁻¹ * x * (x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m) * _
        rw [map_mul]
        group
      refine ⟨m * p, (hUI _).1 (U.mul_mem ((hUI _).2 hm) hp), ?_, ?_⟩
      · rw [hfmp]; exact (hUI _).1 hcU
      · rw [hfmp]; exact hcD
  have hSd : ∀ j, S (j + 1) ⊆ S j := fun j m hm => ⟨hm.1, hm.2.1, fun i l h =>
    (hm.2.2 i l h).trans (pow_le_pow_right_of_le_one' hρ1.le (Nat.le_succ j))⟩
  have hS0 : IsCompact (S 0) := hcpt.of_isClosed_subset (hSc 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn hS0 hSc
  have hm' : ∀ j, m ∈ S j := Set.mem_iInter.1 hm
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨m, (hm' 0).1, f m, ⟨(hm' 0).2.1.1, fun i l hil => ?_⟩, ?_⟩
  · by_contra h0
    have hv : valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hρ1 (Units.mk0 _ hv)
    exact absurd ((hm' j).2.2 i l hil) (not_le.2 hj)
  · show _ = x * (x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m)
    group

end Main

end GlobalTheory.CompanionTheory.TwContraction
