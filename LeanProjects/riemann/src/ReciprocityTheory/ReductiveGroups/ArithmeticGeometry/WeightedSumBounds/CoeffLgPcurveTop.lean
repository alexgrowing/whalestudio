import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.LgCurvePcurve

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem coeff_lg_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) (m : ℕ) :
    PowerSeries.coeff m (G.lgCurve (pcurve G p γ x n) a) = ∑ s ∈ Finset.range n, ∑ b,
      if p ^ s ∣ m then x s b ^ (m / p ^ s) * PowerSeries.coeff (m / p ^ s) (G.lgCurve (γ b) a)
      else 0 := by
  rw [lgCurve_pcurve G hp hγ x n hx a, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [coeff_expand_rescale]

theorem lg_agree (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hga : G.IsPTypical p ga) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b)) :
    ∀ a, ∀ j < p ^ n, PowerSeries.coeff j (G.lgCurve ga a) =
      PowerSeries.coeff j (G.lgCurve (pcurve G p γ (ptx G p γ ga) n) a) := by
  intro a j hj
  rw [coeff_lg_pcurve G hp.ne_zero hγ _ n hx a j]
  by_cases hpow : ∃ m, j = p ^ m
  · obtain ⟨m, rfl⟩ := hpow
    have hmn : m < n := by
      by_contra h
      push_neg at h
      exact absurd hj (not_lt.mpr (Nat.pow_le_pow_right hp.pos h))
    have hrel := congrFun (ptx_rel G p hγ hdet ga m) a
    change G.lc p ga m a = _
    rw [hrel]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ n by omega)]
    have hzero : ∑ s ∈ Finset.Ico (m + 1) n, ∑ b, (if p ^ s ∣ p ^ m then
        ptx G p γ ga s b ^ (p ^ m / p ^ s) * PowerSeries.coeff (p ^ m / p ^ s) (G.lgCurve (γ b) a)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hs' : m < s := by
        rw [Finset.mem_Ico] at hs
        omega
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hd
      have hle : s ≤ m := by
        first
        | exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
        | exact (Nat.pow_dvd_pow_iff_le_right' ).mp hd
      omega
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro s hs
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    apply Finset.sum_congr rfl
    intro b _
    rw [if_pos (pow_dvd_pow p hsm), Nat.pow_div hsm hp.pos]
    rfl
  · push_neg at hpow
    rw [hga a j hpow]
    symm
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hd
    · obtain ⟨k, hk⟩ := hd
      have hk' : j / p ^ s = k := by
        rw [hk, Nat.mul_div_cancel_left _ (pow_pos hp.pos s)]
      have hnp : ∀ m', k ≠ p ^ m' := by
        intro m' hm'
        apply hpow (s + m')
        rw [hk, hm', pow_add]
      rw [hk', hγt b a k hnp, mul_zero]
    · rfl

theorem coeff_lg_pcurve_top (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) :
    PowerSeries.coeff (p ^ n) (G.lgCurve (pcurve G p γ x n) a) =
      (∑ s ∈ Finset.range n, ∑ b, (x s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) a := by
  rw [coeff_lg_pcurve G hp.ne_zero hγ x n hx a (p ^ n)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsn : s ≤ n := (Finset.mem_range.mp hs).le
  apply Finset.sum_congr rfl
  intro b _
  rw [if_pos (pow_dvd_pow p hsn), Nat.pow_div hsn hp.pos]
  rfl

private theorem exists_subring_mem_iff_isIntV : ∃ S : Subring C, ∀ x, x ∈ S ↔ IsIntV v x :=
  ⟨{ carrier := {x | 0 ≤ v x}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
       exact add_nonneg ha hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }, fun _ => Iff.rfl⟩

theorem ptx_int (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hgaC : IsCurve v ga) (hga : G.IsPTypical p ga) :
    ∀ n b, IsIntV v (ptx G p γ ga n b) := by
  obtain ⟨S, hS⟩ := exists_subring_mem_iff_isIntV (v := v)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b
    have hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b) := fun s hs b => ih s hs b
    have hagree := lg_agree G hp hγ hγt hdet ga hga n hx
    have hα : ∀ c, PowerSeries.constantCoeff (ga c) = 0 := fun c => (hgaC c).1
    have hpcC := isCurve_pcurve G hp.ne_zero hγ (ptx G p γ ga) n hx
    have hβ : ∀ c, PowerSeries.constantCoeff (pcurve G p γ (ptx G p γ ga) n c) = 0 :=
      fun c => (hpcC c).1
    have hw : ∀ c, IsIntV v (ptw G p γ ga n c) := by
      intro c
      have h1 := coeff_lgCurve_sub_eq G hα hβ (p ^ n) hagree c
      have h2 := coeff_lg_pcurve_top G hp hγ (ptx G p γ ga) n hx c
      have e : ptw G p γ ga n c =
          PowerSeries.coeff (p ^ n) (ga c - pcurve G p γ (ptx G p γ ga) n c) := by
        rw [← h1, map_sub, h2]
        simp only [ptw, Pi.sub_apply]
        rfl
      rw [e, ← hS, map_sub]
      exact S.sub_mem ((hS _).2 ((hgaC c).2 _)) ((hS _).2 ((hpcC c).2 _))
    rw [ptx_eq]
    exact isIntV_vecMul_inv hγ hdet hw b

private theorem lgCurve_const_zero (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by simp)
  ext j
  rw [map_zero]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst _ (G.lg a)) = 0
  rw [MvPowerSeries.coeff_subst h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · subst he
    rw [coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]

private theorem lc_zero_eq_tangent_of_constantCoeff_eq_zero (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_const_zero, sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]

theorem ptx_type {h : ℕ} (ty : Fin d → ZMod h) (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0)
    (hγty : ∀ b, G.IsOfType p ty (ty b) (γ b)) (ga : Fin d → PowerSeries C) (i : ZMod h)
    (hga : G.IsOfType p ty i ga) :
    ∀ n b, ptx G p γ ga n b ≠ 0 → ty b = i + n := by
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    have h0 := (hγty b).2 0 c (by simpa using hc)
    rwa [lc_zero_eq_tangent_of_constantCoeff_eq_zero G p (γ b) (fun c' => (hγ b c').1)] at h0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hw : ∀ c, ty c ≠ i + n → Matrix.vecMul (ptx G p γ ga n) (tmat γ) c = 0 := by
      intro c hc
      rw [ptx_eq, vecMul_inv_tmat hdet]
      simp only [ptw, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hga.2 n c hc, zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro s hs
      have hsn : s < n := Finset.mem_range.mp hs
      apply Finset.sum_eq_zero
      intro b _
      by_cases hx0 : ptx G p γ ga s b = 0
      · rw [hx0, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
      · have htb := ih s hsn b hx0
        have hlc : G.lc p (γ b) (n - s) c = 0 := by
          apply (hγty b).2 (n - s) c
          rw [htb, Nat.cast_sub hsn.le]
          intro h'
          apply hc
          rw [h']
          ring
        rw [hlc, mul_zero]
    intro b hb
    by_contra hne
    exact hb (vecMul_tmat_support ty hdet ht (ptx G p γ ga n) (i + n) hw b hne)

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
