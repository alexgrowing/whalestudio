import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix

open MeasureTheory Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

def hσ (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

def hs (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

private lemma hsig_val_eq_ite (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (hσ k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold hσ
  split_ifs <;> rfl

lemma hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hσ k r i then hs k r i else 0 := by
  unfold Hpk hσ hs
  have hi := i.isLt
  have hj := j.isLt
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    have hne : i.val ≠ r + k := by omega
    by_cases h2 : j.val = 2 * r + k - i.val
    · have : j = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext h2
      rw [if_pos this, if_neg hne]
      rcases h1 with h1 | h1
      · rw [if_pos ⟨h1, by omega⟩]
      · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    · have : j ≠ ⟨2 * r + k - i.val, by omega⟩ := fun h => h2 (by rw [h])
      rw [if_neg this, if_neg (by omega), if_neg (by omega), if_neg]
      rintro ⟨_, _, h3⟩
      exact h2 (by rw [h3]; omega)
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h3 : j = i
    · subst h3
      simp [h1.1, h1.2]
    · rw [if_neg h3, if_neg]
      rintro ⟨_, _, h4⟩
      exact h3 h4.symm

lemma hσ_hσ (k r : ℕ) (i : Fin (2 * r + k + 1)) : hσ k r (hσ k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [hsig_val_eq_ite, hsig_val_eq_ite]
  split_ifs <;> omega

lemma hs_mul (k r : ℕ) (i : Fin (2 * r + k + 1)) : hs k r i * hs k r (hσ k r i) = 1 := by
  have hi := i.isLt
  simp only [hs, hsig_val_eq_ite]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (hσ k r i)]
  · rw [hpk_eq, hpk_eq, if_pos rfl, hσ_hσ, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      exact hs_mul k r _
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · intro l _ hl
    rw [hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma hs_hσ (k r : ℕ) (i : Fin (2 * r + k + 1)) : hs k r (hσ k r i) = hs k r i := by
  have hi := i.isLt
  simp only [hs, hsig_val_eq_ite]
  split_ifs <;> first | (exfalso; omega) | rfl

lemma star_hs (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hs k r i) = hs k r i := by
  simp only [hs]
  split_ifs <;> simp

lemma hσ_eq_iff (k r : ℕ) (i j : Fin (2 * r + k + 1)) : i = hσ k r j ↔ j = hσ k r i := by
  constructor
  · rintro rfl
    exact (hσ_hσ k r j).symm
  · rintro rfl
    exact (hσ_hσ k r i).symm

lemma hpk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, hpk_eq, hpk_eq]
  by_cases h : j = hσ k r i
  · subst h
    rw [if_pos (hσ_hσ k r i).symm, if_pos rfl, star_hs, hs_hσ]
  · rw [if_neg (fun h' => h ((hσ_eq_iff k r i j).1 h')), if_neg h, star_zero]

lemma hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (hpk_mul_self k r)

lemma uh_mul {k r : ℕ} {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma uh_det {k r : ℕ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  refine Matrix.isUnit_det_of_left_inverse (B := Hpk k r * aᴴ * Hpk k r) ?_
  calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ha', hpk_mul_self]

lemma uh_inv {k r : ℕ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hd : IsUnit a.det := uh_det ha
  have hd' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hd.star
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  rw [Matrix.conjTranspose_nonsing_inv]
  calc (aᴴ)⁻¹ * Hpk k r * a⁻¹ = (aᴴ)⁻¹ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = ((aᴴ)⁻¹ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.nonsing_inv_mul _ hd', Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]

lemma hpk_mem (k r : ℕ) : Hpk k r ∈ UH (Hpk k r) := by
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [hpk_conjTranspose, hpk_mul_self, Matrix.one_mul]

private lemma isClosed_UH' (k r : ℕ) : IsClosed (UH (Hpk k r)) := by
  rw [UH.eq_1]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

private lemma one_mem_dualWeyl_complex (k r : ℕ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  rw [UH.eq_1]
  simp

theorem unitary_hermitian_group : UHGroup := by
  intro k r
  unfold IsMatGroup
  exact ⟨isClosed_UH' k r, one_mem_dualWeyl_complex k r, fun a ha b hb => uh_mul ha hb,
    fun a ha => ⟨uh_inv ha, Matrix.mul_nonsing_inv _ (uh_det ha)⟩⟩

theorem siegel_set_subset : SsetSub := by
  intro k r z s hsx
  rw [Sset.eq_1, Set.mem_setOf_eq] at hsx
  obtain ⟨h, hh, m, hm, rfl⟩ := hsx
  rw [UWset.eq_1, Set.mem_setOf_eq] at hh
  rw [Nset.eq_1, Set.mem_setOf_eq] at hm
  exact uh_mul hh.1 hm.1

theorem maximal_compact_isCompact : KCompact := by
  intro k r
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have c2 : IsClosed {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | uᴴ * u = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hC : IsClosed {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      u ∈ UH (Hpk k r) ∧ uᴴ * u = 1} := (isClosed_UH' k r).inter c2
  refine hK.of_isClosed_subset hC
    (fun (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) hu => ?_)
  have hu' : u ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu.2
  exact Set.mem_pi.2 fun i _ => Set.mem_pi.2 fun j _ =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hu' i j)

lemma pow_bdd_le_one {x M : ℝ} (hx : 0 < x) (h : ∀ n : ℕ, x ^ n ≤ M) : x ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  exact absurd (h n) (not_le.2 hn)

theorem trivG_of (hPol : PolarUH) (hK : KCompact) : TrivG := by
  intro k r D hD g hg
  rw [ModProps.eq_1] at hD
  obtain ⟨hpos, hmul, hconj, hbdd⟩ := hD
  have hH : Hpk k r ∈ UH (Hpk k r) := hpk_mem k r
  have one_mem := one_mem_dualWeyl_complex k r
  have hD1 : D 1 = 1 := by
    have h1 := hmul 1 one_mem 1 one_mem
    rw [Matrix.one_mul] at h1
    have h0 := hpos 1 one_mem
    exact mul_left_cancel₀ h0.ne' (h1.symm.trans (mul_one (D 1)).symm)
  have inv_D : ∀ x ∈ UH (Hpk k r), D x * D x⁻¹ = 1 := by
    intro x hx
    rw [← hmul x hx x⁻¹ (uh_inv hx), Matrix.mul_nonsing_inv x (uh_det hx), hD1]
  obtain ⟨M, hM⟩ := hbdd {u | u ∈ UH (Hpk k r) ∧ uᴴ * u = 1} (fun v hv => hv.1) (hK k r)
  have powle : ∀ v, v ∈ UH (Hpk k r) → vᴴ * v = 1 → D v ≤ 1 := by
    intro v hv hvu
    have hvn : ∀ n : ℕ, v ^ n ∈ UH (Hpk k r) ∧ (v ^ n)ᴴ * v ^ n = 1 ∧ D (v ^ n) = D v ^ n := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [pow_zero]; exact one_mem, by rw [pow_zero]; simp, ?_⟩
        rw [pow_zero v, pow_zero (D v)]
        exact hD1
      | succ n ih =>
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨by rw [pow_succ]; exact uh_mul h1 hv, ?_, ?_⟩
        · rw [pow_succ, Matrix.conjTranspose_mul]
          calc vᴴ * (v ^ n)ᴴ * (v ^ n * v) = vᴴ * ((v ^ n)ᴴ * v ^ n) * v := by
                simp only [Matrix.mul_assoc]
            _ = 1 := by rw [h2, Matrix.mul_one, hvu]
        · rw [pow_succ v n, hmul _ h1 _ hv, h3, pow_succ (D v) n]
    refine pow_bdd_le_one (M := M) (hpos v hv) (fun n => ?_)
    rw [← (hvn n).2.2]
    exact hM _ ⟨(hvn n).1, (hvn n).2.1⟩
  obtain ⟨u, p, hu, huu, hp, hph, rfl⟩ := hPol k r g hg
  have hu1 : D u = 1 := by
    have hui : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv huu
    have hdu : IsUnit u.det := Matrix.isUnit_det_of_left_inverse huu
    have a1 := powle u hu huu
    have a2 := powle u⁻¹ (uh_inv hu) (by
      rw [hui, Matrix.conjTranspose_conjTranspose, ← hui]
      exact Matrix.mul_nonsing_inv u hdu)
    have a3 := inv_D u hu
    have a4 := hpos u hu
    have a5 := hpos u⁻¹ (uh_inv hu)
    nlinarith
  have hHunit : IsUnit (Hpk k r) := (Matrix.isUnit_iff_isUnit_det _).2 (uh_det hH)
  have hnorm : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Hpk k r * x * (Hpk k r)⁻¹ ∈ UH (Hpk k r) ↔ x ∈ UH (Hpk k r) := by
    intro x
    rw [hpk_inv]
    constructor
    · intro hx
      have h4 := uh_mul (uh_mul hH hx) hH
      have e : Hpk k r * (Hpk k r * x * Hpk k r) * Hpk k r = x := by
        calc Hpk k r * (Hpk k r * x * Hpk k r) * Hpk k r
            = (Hpk k r * Hpk k r) * x * (Hpk k r * Hpk k r) := by simp only [Matrix.mul_assoc]
          _ = x := by rw [hpk_mul_self, Matrix.one_mul, Matrix.mul_one]
      rwa [e] at h4
    · intro hx
      exact uh_mul (uh_mul hH hx) hH
  have hp1 : D p = 1 := by
    have hpH : p * Hpk k r * p = Hpk k r := by
      have h0 : pᴴ * Hpk k r * p = Hpk k r := hp
      rwa [hph] at h0
    have hpinv : p⁻¹ = Hpk k r * p * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * p * Hpk k r * p = Hpk k r * (p * Hpk k r * p) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hpH, hpk_mul_self]
    have e1 := hconj (Hpk k r) hHunit hnorm p hp
    rw [hpk_inv, ← hpinv] at e1
    have a3 := inv_D p hp
    rw [e1] at a3
    have a4 := hpos p hp
    nlinarith
  rw [hmul u hu p hp, hu1, hp1, one_mul]

end PI.QuotSetU.UnitaryGroupMassFormula

end
