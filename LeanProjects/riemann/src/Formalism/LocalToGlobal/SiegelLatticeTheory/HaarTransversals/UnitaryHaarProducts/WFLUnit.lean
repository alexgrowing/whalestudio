import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace

set_option linter.unusedSimpArgs false

namespace Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

section Unit
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

private theorem Hpk_apply_eq_zero_of_ne_sig (p b : Fin (2 * r + k + 1)) (hb : b ≠ GBasic.sig k r p) :
    Hpk k r p b = 0 := by
  have hb' : b.val ≠ (GBasic.sig k r p).val := fun h => hb (Fin.ext h)
  unfold GBasic.sig at hb'
  unfold Hpk
  split_ifs at hb' ⊢ <;> (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq] at *) <;> omega

private theorem Hpk_apply_sig_ne_zero (p : Fin (2 * r + k + 1)) : Hpk k r p (GBasic.sig k r p) ≠ 0 := by
  have hp := p.isLt
  unfold Hpk GBasic.sig
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq] at *) <;>
    first | omega | (simp only [and_true] at *; omega) | norm_num

theorem fix_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : h ∈ UH (Hpk k r))
    {p : Fin (2 * r + k + 1)} (hp : h *ᵥ bvec p = bvec p) (j : Fin (2 * r + k + 1)) :
    h (GBasic.sig k r p) j = if j = GBasic.sig k r p then 1 else 0 := by
  have hU0 : hᴴ * Hpk k r * h = Hpk k r := hU
  have hcol : ∀ a, h a p = if a = p then 1 else 0 := by
    intro a
    have := congrFun hp a
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have key : (hᴴ * Hpk k r * h) p j = Hpk k r p (GBasic.sig k r p) * h (GBasic.sig k r p) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r p)]
    · congr 1
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · simp [hcol]
      · intro a _ ha
        simp [hcol, ha]
      · simp
    · intro b _ hb
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · simp [Hpk_apply_eq_zero_of_ne_sig p b hb]
      · intro a _ ha
        simp [hcol, ha]
      · simp
    · simp
  have e : Hpk k r p (GBasic.sig k r p) * h (GBasic.sig k r p) j = Hpk k r p j := by
    rw [← key, hU0]
  by_cases hj : j = GBasic.sig k r p
  · subst hj
    rw [if_pos rfl]
    have e1 : Hpk k r p (GBasic.sig k r p) * h (GBasic.sig k r p) (GBasic.sig k r p) =
        Hpk k r p (GBasic.sig k r p) * 1 := by rw [mul_one]; exact e
    exact mul_left_cancel₀ (Hpk_apply_sig_ne_zero p) e1
  · rw [if_neg hj]
    rw [Hpk_apply_eq_zero_of_ne_sig p j hj] at e
    exact (mul_eq_zero.mp e).resolve_left (Hpk_apply_sig_ne_zero p)

theorem wI_last_eq : wI k r (Fin.last k) = GBasic.sig k r (wI k r (Fin.last k)) := by
  unfold GBasic.sig
  have hn : ¬ ((wI k r (Fin.last k)).val < r ∨ r + k < (wI k r (Fin.last k)).val) := by
    simp [wI]
  rw [if_neg hn]

theorem UW_colW {T : ℝ} (hT : 0 < T) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r (zBv k r T)) (b : Fin k) (t : Fin (2 * r + k + 1))
    (ht : ∀ a : Fin k, t ≠ wI k r ⟨a.val, by omega⟩) : h t (wI k r ⟨b.val, by omega⟩) = 0 := by
  unfold zBv at hh
  obtain ⟨hU, hfix, hz⟩ := hh
  have hb := b.isLt
  have key : ∃ p, h *ᵥ bvec p = bvec p ∧ GBasic.sig k r p = t := by
    by_cases h1 : t.val < r
    · refine ⟨esI k r ⟨t.val, h1⟩, (hfix _).2, ?_⟩
      ext
      unfold GBasic.sig
      split_ifs with hc <;> simp only [esI, Fin.val_mk] at hc ⊢ <;> omega
    · by_cases h2 : r + k < t.val
      · have ht2 := t.isLt
        refine ⟨eI k r ⟨2 * r + k - t.val, by omega⟩, (hfix _).1, ?_⟩
        ext
        unfold GBasic.sig
        split_ifs with hc <;> simp only [eI, Fin.val_mk] at hc ⊢ <;> omega
      · have h3 : t = wI k r (Fin.last k) := by
          ext
          simp only [wI, Fin.val_last]
          by_contra hne
          exact ht ⟨t.val - r, by omega⟩ (by ext; simp only [wI]; omega)
        refine ⟨wI k r (Fin.last k), ?_, ?_⟩
        · have hs : ((√T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hT).ne'
          rw [Matrix.mulVec_smul] at hz
          exact smul_right_injective (Fin (2 * r + k + 1) → ℂ) hs hz
        · rw [h3]
          exact wI_last_eq.symm
  obtain ⟨p, hp, rfl⟩ := key
  rw [fix_row hU hp, if_neg (fun hq => ht b hq.symm)]

end Unit

section Unit2
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

private theorem hJ_eq_star_hJ_swap {n : ℕ} (ε1 : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε1 x y = star (hJ ε1 y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_one, star_neg] <;> ring

private theorem conjTranspose_Qm_mulVec_Jm_apply_eq_hJ_colQ (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (2 * r + k + 1)) :
    ((Qm e f wf z0)ᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y)) t = hJ ε (colQ e f wf z0 t) y := by
  unfold hJ
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Qm, Matrix.of_apply, Pi.star_apply]

private theorem Hpk_apply_middle_right_eq_ite (t' t : Fin (2 * r + k + 1)) (h1 : r ≤ t.val) (h2 : t.val < r + k) :
    Hpk k r t' t = if t' = t then 1 else 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num

private theorem hJ_Qm_mulVec_eq_sum (x c : Fin (2 * r + k + 1) → ℂ) :
    hJ ε x (Qm e f wf z0 *ᵥ c) = ∑ t, c t * hJ ε x (colQ e f wf z0 t) := by
  have hq : Qm e f wf z0 *ᵥ c = ∑ t, c t • colQ e f wf z0 t := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  rw [hq]
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem piB_entry (hF : IsFrameJ ε e f wf z0) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin k) :
    hJ ε (wf a) ((Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ wf b) = h (wI k r ⟨a.val, by omega⟩) (wI k r ⟨b.val, by omega⟩) := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hww, hew, hfw, hzw⟩ := hF
  have hcol : ∀ t (c : Fin k), hJ ε (colQ e f wf z0 t) (wf c) =
      if t = wI k r ⟨c.val, by omega⟩ then 1 else 0 := by
    intro t c
    have ht := t.isLt
    have hc := c.isLt
    have hw : (wI k r ⟨c.val, by omega⟩).val = r + c.val := rfl
    unfold colQ
    split_ifs <;> simp only [hew, hfw, hzw, hww, Fin.ext_iff, wI, Fin.val_mk] <;> (try split_ifs) <;>
      first | rfl | omega | (exfalso; omega)
  have v1 : (Qm e f wf z0)ᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ wf b) = bvec (wI k r ⟨b.val, by omega⟩) := by
    ext t
    rw [conjTranspose_Qm_mulVec_Jm_apply_eq_hJ_colQ, hcol]
    simp only [bvec, Pi.single_apply]
  have v2 : Hpk k r *ᵥ bvec (wI k r ⟨b.val, by omega⟩) = bvec (wI k r ⟨b.val, by omega⟩) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Hpk_apply_middle_right_eq_ite i _ (by simp only [wI]; omega) (by simp only [wI]; omega)
  have v3 : h *ᵥ bvec (wI k r ⟨b.val, by omega⟩) = fun t => h t (wI k r ⟨b.val, by omega⟩) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold Qi
  simp only [← Matrix.mulVec_mulVec]
  rw [v1, v2, v3, hJ_Qm_mulVec_eq_sum]
  rw [Finset.sum_eq_single (wI k r ⟨a.val, by omega⟩)]
  · rw [hJ_eq_star_hJ_swap, hcol, if_pos rfl, star_one, mul_one]
  · intro t _ ht
    rw [hJ_eq_star_hJ_swap, hcol, if_neg ht, star_zero, mul_zero]
  · simp

theorem Jm_allPos : Formalism.REAL.Jm (allPos k) = 1 := by
  ext a b
  simp [Formalism.REAL.Jm, allPos, Matrix.diagonal, Matrix.one_apply]

private theorem Hpk_apply_middle_left_eq_ite (t t' : Fin (2 * r + k + 1)) (h1 : r ≤ t.val) (h2 : t.val < r + k) :
    Hpk k r t t' = if t' = t then 1 else 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num

theorem piB_mat_unitary (hF : IsFrameJ ε e f wf z0) {T : ℝ} (hT : 0 < T)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r (zBv k r T)) :
    (fun a b => hJ ε (wf a) ((Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ wf b)) ∈ UJset (allPos k) := by
  have hM : (fun a b => hJ ε (wf a) ((Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ wf b)) =
      (fun a b => h (wI k r ⟨a.val, by omega⟩) (wI k r ⟨b.val, by omega⟩) : Matrix (Fin k) (Fin k) ℂ) := by
    funext a b
    exact piB_entry hF h a b
  rw [hM]
  show Formalism.REAL.inUJ _ _
  unfold Formalism.REAL.inUJ
  rw [Jm_allPos, Matrix.mul_one]
  have hU0 : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hz : ∀ (c : Fin k) (t : Fin (2 * r + k + 1)), ¬ (r ≤ t.val ∧ t.val < r + k) →
      h t (wI k r ⟨c.val, by omega⟩) = 0 := by
    intro c t ht
    apply UW_colW hT hh c t
    intro a hta
    apply ht
    have := congrArg Fin.val hta
    simp only [wI] at this
    omega
  have hrow : ∀ (c : Fin k) (t' : Fin (2 * r + k + 1)),
      (hᴴ * Hpk k r) (wI k r ⟨c.val, by omega⟩) t' = star (h t' (wI k r ⟨c.val, by omega⟩)) := by
    intro c t'
    rw [Matrix.mul_apply, Finset.sum_eq_single t']
    · simp only [Matrix.conjTranspose_apply]
      by_cases hw : r ≤ t'.val ∧ t'.val < r + k
      · rw [Hpk_apply_middle_left_eq_ite t' t' hw.1 hw.2, if_pos rfl, mul_one]
      · rw [hz c t' hw]
        simp
    · intro t _ hne
      simp only [Matrix.conjTranspose_apply]
      by_cases hw : r ≤ t.val ∧ t.val < r + k
      · rw [Hpk_apply_middle_left_eq_ite t t' hw.1 hw.2, if_neg (Ne.symm hne), mul_zero]
      · rw [hz c t hw]
        simp
    · simp
  ext a b
  have e := congrFun (congrFun hU0 (wI k r ⟨a.val, by omega⟩)) (wI k r ⟨b.val, by omega⟩)
  rw [Matrix.mul_apply] at e
  simp only [hrow] at e
  rw [Hpk_apply_middle_left_eq_ite (wI k r ⟨a.val, by omega⟩) (wI k r ⟨b.val, by omega⟩)
    (by simp only [wI]; omega) (by simp only [wI]; omega)] at e
  have hinj : Function.Injective (fun c : Fin k => wI k r ⟨c.val, by omega⟩) := by
    intro c c' hcc
    have := congrArg Fin.val hcc
    simp only [wI] at this
    exact Fin.ext (by omega)
  have hzero : ∀ x ∉ Set.range (fun c : Fin k => wI k r ⟨c.val, by omega⟩),
      star (h x (wI k r ⟨a.val, by omega⟩)) * h x (wI k r ⟨b.val, by omega⟩) = 0 := by
    intro x hx
    have hw : ¬ (r ≤ x.val ∧ x.val < r + k) := by
      rintro ⟨h1, h2⟩
      exact hx ⟨⟨x.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩
    rw [hz a x hw]
    simp
  have hsum := Fintype.sum_of_injective _ hinj _ _ hzero (fun c => rfl)
  have hab : (a = b) ↔ (wI k r ⟨b.val, by omega⟩ = wI k r ⟨a.val, by omega⟩) := by
    constructor
    · rintro rfl
      rfl
    · intro hh'
      have := congrArg Fin.val hh'
      simp only [wI] at this
      exact Fin.ext (by omega)
  change ∑ c : Fin k, star (h (wI k r ⟨c.val, by omega⟩) (wI k r ⟨a.val, by omega⟩)) *
      h (wI k r ⟨c.val, by omega⟩) (wI k r ⟨b.val, by omega⟩) = (if a = b then 1 else 0)
  rw [if_congr hab rfl rfl]
  exact hsum.trans e

theorem piB_norm (hF : IsFrameJ ε e f wf z0) {T : ℝ} (hT : 0 < T) {u : Fin k → ℝ}
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)}
    (hπ : IsHCTypeU k u πl) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r (zBv k r T)) (x : V) : ‖piB ε e f wf z0 πl h x‖ = ‖x‖ := by
  unfold piB
  exact hπ.2.2.1.2.1 _ (piB_mat_unitary hF hT hh) x

theorem psiR_norm {n r' : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r' → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  exact Formalism.L2.SG.Pf.psiR_norm ε gg e f z g

end Unit2

section Inv
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ}

theorem loc_norm_inv {T : ℝ} (hT : 0 < T) {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z))
    {gg : ℕ} {u : Fin k → ℝ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hπ : IsHCTypeU k u πl) {W : Formalism.REAL.UJ ε → V}
    (hW : ∀ s x : Formalism.REAL.UJ ε, ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
      Qi ε e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h * m →
      W (s * x) = psiR ε gg e f z (uMat s) • piB ε e f wf (z0v T z) πl h (W x))
    {s : Formalism.REAL.UJ ε} (hs : s ∈ HNset ε e f wf (z0v T z) (zBv k r T)) (y : Formalism.REAL.UJ ε) :
    ‖W (s * y)‖ = ‖W y‖ := by
  unfold HNset at hs
  obtain ⟨h, hh, m, hm, hhm⟩ := hs
  rw [hW s y h hh m hm hhm, norm_smul, psiR_norm, one_mul]
  exact piB_norm hF hT hπ hh (W y)

end Inv

section Assembly
open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ConcreteSettingExists
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mEqR (R : Ranks) : 2 * R.rS + 2 = R.m := by
  obtain ⟨j, hj⟩ := R.m_even
  have h2 := R.two_le_m
  show 2 * (R.m / 2 - 1) + 2 = R.m
  omega

theorem lam_matchR (R : Ranks) (P : HCParam R) (i : Fin (2 * R.rS + R.k + 1)) (hr : 2 * R.rS + R.k + 1 = R.r) :
    lamS R P (Fin.cast hr i) =
      lam48 R.k R.rS (fun i => (P.v i : ℝ)) (fun j => (P.b (Fin.cast (mEqR R) j) : ℝ)) i := by
  have hm := mEqR R
  have hk := R.m_add_three_le_k
  have hi := i.isLt
  unfold lamS lam48
  simp only [Fin.coe_cast]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem interlace_of (R : Ranks) (P Q : HCParam R) (hv : Q.v = P.v) (hb : Q.b = P.b) :
    InterlacingCondition R.k R.rS (fun i => (Q.u i : ℝ)) (fun i => (P.v i : ℝ)) (fun j => (P.b (Fin.cast (mEqR R) j) : ℝ)) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := Q.u_gt_v i
    rw [hv] at this
    dsimp only
    exact_mod_cast this
  · have := Q.v_gt_u i
    rw [hv] at this
    dsimp only
    exact_mod_cast this
  · have h2 := R.two_le_m
    have := Q.u_last_gt h (by omega)
    rw [hb] at this
    simp only [Fin.cast_mk]
    exact_mod_cast this

theorem halfInt_of (R : Ranks) (P Q : HCParam R) :
    HalfIntegralDifference R.k R.rS (fun i => (Q.u i : ℝ)) (fun i => (P.v i : ℝ)) (fun j => (P.b (Fin.cast (mEqR R) j) : ℝ)) := by
  intro i s
  choose gv hgv using P.v_int
  choose gb hgb using P.b_int
  obtain ⟨a, ha⟩ := Q.u_half i
  unfold lam48
  dsimp only
  split_ifs with h
  · refine ⟨a - gv ⟨s.val, h⟩, ?_⟩
    rw [ha, hgv]
    push_cast
    ring
  · refine ⟨a + gb (Fin.cast (mEqR R) ⟨s.val - (R.k - 1), by have := s.isLt; omega⟩), ?_⟩
    simp only [ha, hgb]
    push_cast
    ring

end Assembly

end Formalism.L2.SG.Pf.WFL
