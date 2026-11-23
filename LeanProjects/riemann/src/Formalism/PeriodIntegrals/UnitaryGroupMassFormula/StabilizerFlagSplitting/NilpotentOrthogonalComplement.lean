import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic

noncomputable section

namespace PI.StabSplit.UnipW

def perpX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r + k < i.val → v i = 0

def inX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0

def Lk (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

lemma mulVec_bvec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ bvec j = fun i => A i j := by
  funext i
  simp [bvec, Matrix.mulVec, Pi.single_apply]

lemma sig_gt {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val < r) : r + k < (sig k r i).val := by
  unfold sig
  rw [if_pos (Or.inl h)]
  show r + k < 2 * r + k - i.val
  omega

lemma sig_ge {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val ≤ r + k) : r ≤ (sig k r i).val := by
  unfold sig
  split_ifs with h'
  · show r ≤ 2 * r + k - i.val
    omega
  · push_neg at h'
    exact h'.1

private lemma hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  by_cases hi : i.val < r ∨ r + k < i.val
  · have hsig : sig k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold sig
      rw [if_pos hi]
    rw [hsig]
    have hj : (j = (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))) ↔ i.val + j.val = 2 * r + k := by
      rw [Fin.ext_iff]
      simp only
      omega
    simp only [Hpk, sgn, hj]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · have hsig : sig k r i = i := by
      unfold sig
      rw [if_neg hi]
    rw [hsig]
    push_neg at hi
    simp only [Hpk, sgn]
    by_cases hij : j = i
    · subst hij
      simp only [if_true, and_true, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hij' : ¬ i = j := fun h => hij h.symm
      simp only [hij, hij', if_false, and_false]
      split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_coord {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (sgn k r i * v (sig k r i)) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, hpk_apply_of_outer_index, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma star_dotProduct_Hpk_mulVec_eq_sum_sub {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) v w =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then star (w i) * (sgn k r i * v i) else 0 := by
  rw [herm_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hs : sig k r i = i := by
      unfold sig
      rw [if_neg (by omega)]
    rw [hs]
  · by_cases hi : i.val < r
    · rw [hv _ (sig_gt i hi)]
      ring
    · rw [hw i (by omega)]
      simp

lemma herm_perp_inX {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) v x = 0 := by
  rw [herm_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r
  · rw [hv _ (sig_gt i hi)]
    ring
  · rw [hx i (by omega)]
    simp

lemma herm_inX_perp {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) x v = 0 := by
  rw [herm_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ r + k
  · rw [hx _ (sig_ge i hi)]
    ring
  · rw [hv i (by omega)]
    simp

lemma star_sgn {k r : ℕ} (i : Fin (2 * r + k + 1)) : star (sgn k r i) = sgn k r i := by
  unfold sgn
  split_ifs <;> simp

lemma herm_conjW {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hv, star_dotProduct_Hpk_mulVec_eq_sum_sub hv hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [star_mul', star_star, star_sgn]
    ring
  · simp

lemma herm_self_re {k r : ℕ} {w : Fin (2 * r + k + 1) → ℂ} (hw : perpX k r w) (hL : w (Lk k r) = 0) :
    (herm (Hpk k r) w w).re =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hw, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · by_cases hi : i.val = r + k
    · have e : i = Lk k r := Fin.ext hi
      rw [e, hL]
      simp
    · simp only [sgn, if_neg hi, one_mul]
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  · simp

lemma sum_W_nonneg {k r : ℕ} (w : Fin (2 * r + k + 1) → ℂ) :
    0 ≤ ∑ i : Fin (2 * r + k + 1), if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := Finset.sum_nonneg fun i _ => by
    split_ifs <;> first | exact Complex.normSq_nonneg _ | exact le_refl _

lemma herm_expand {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (y z : Fin m → ℂ) (c : ℂ) :
    herm H (y - c • z) (y - c • z) =
      herm H y y - star c * herm H y z - c * herm H z y + c * star c * herm H z z := by
  unfold herm
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma herm_add_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

lemma herm_add_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v a b : Fin m → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  unfold herm
  rw [star_add, add_dotProduct]

lemma herm_sub_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a - b) w = herm H a w - herm H b w := by
  unfold herm
  rw [Matrix.mulVec_sub, dotProduct_sub]

lemma herm_inv {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ} (hg : gᴴ * H * g = H) (v w : Fin m → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  first | rw [hg] | rw [← Matrix.mul_assoc, hg]

lemma definite {k r : ℕ} {y z : Fin (2 * r + k + 1) → ℂ} (hy : perpX k r y) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (h1 : herm (Hpk k r) y y = 0) (h2 : herm (Hpk k r) y z = 0) : inX k r y := by
  have hzp : perpX k r z := fun i hi => hz i (Or.inr hi)
  have hzL : z (Lk k r) ≠ 0 := by
    intro h0
    have hnn : 0 ≤ (herm (Hpk k r) z z).re := by rw [herm_self_re hzp h0]; exact sum_W_nonneg z
    unfold Tz at hT; linarith
  set c := y (Lk k r) / z (Lk k r) with hc
  have hwp : perpX k r (y - c • z) := fun i hi => by simp [hy i hi, hzp i hi]
  have hwL : (y - c • z) (Lk k r) = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, div_mul_cancel₀ _ hzL, sub_self]
  have hzy : herm (Hpk k r) z y = 0 := by rw [herm_conjW hy hzp, h2, star_zero]
  have hexp : herm (Hpk k r) (y - c • z) (y - c • z) = (Complex.normSq c : ℂ) * herm (Hpk k r) z z := by
    rw [herm_expand, h1, h2, hzy, Complex.star_def, Complex.mul_conj]; ring
  have hre : (herm (Hpk k r) (y - c • z) (y - c • z)).re = -(Complex.normSq c * Tz k r z) := by
    rw [hexp, Complex.re_ofReal_mul]; unfold Tz; ring
  have hnn : 0 ≤ (herm (Hpk k r) (y - c • z) (y - c • z)).re := by
    rw [herm_self_re hwp hwL]; exact sum_W_nonneg _
  have hc0 : Complex.normSq c = 0 := by
    by_contra hne
    have hpos : 0 < Complex.normSq c := lt_of_le_of_ne (Complex.normSq_nonneg c) (Ne.symm hne)
    have := mul_pos hpos hT
    linarith
  have hyL : y (Lk k r) = 0 := by
    have h0 := Complex.normSq_eq_zero.mp hc0
    rw [hc, div_eq_zero_iff] at h0
    exact h0.resolve_right hzL
  have hsum := herm_self_re hy hyL
  rw [h1, Complex.zero_re] at hsum
  intro i hi
  by_cases hik : r + k < i.val
  · exact hy i hik
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      split_ifs <;> [exact Complex.normSq_nonneg _; exact le_refl _])).mp hsum.symm i (Finset.mem_univ _)
    rw [if_pos ⟨hi, by omega⟩] at hall
    exact Complex.normSq_eq_zero.mp hall

lemma key {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hgU : gᴴ * Hpk k r * g = Hpk k r)
    (hperp : ∀ v, perpX k r v → perpX k r (g *ᵥ v)) (hgz : inX k r (g *ᵥ z - z)) :
    ∀ q : ℕ, ∀ v, perpX k r v → (g - 1) ^ q *ᵥ v = 0 → inX k r (g *ᵥ v - v) := by
  intro q
  induction q with
  | zero =>
    intro v _ hv0
    rw [pow_zero, Matrix.one_mulVec] at hv0
    subst hv0
    intro i _
    simp
  | succ q ih =>
    intro v hv hq
    have hv' : perpX k r (g *ᵥ v - v) := fun i hi => by
      simp only [Pi.sub_apply]
      rw [hperp v hv i hi, hv i hi, sub_zero]
    have hgv : (g - 1) *ᵥ v = g *ᵥ v - v := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hq' : (g - 1) ^ q *ᵥ (g *ᵥ v - v) = 0 := by
      rw [← hgv, Matrix.mulVec_mulVec, ← pow_succ]
      exact hq
    have hx := ih (g *ᵥ v - v) hv' hq'
    set v' := g *ᵥ v - v with hv'def
    set x := g *ᵥ v' - v' with hxdef
    have hgv' : g *ᵥ v' = v' + x := by rw [hxdef]; abel
    have hgv2 : g *ᵥ v = v + v' := by rw [hv'def]; abel
    have e1 := herm_inv hgU v' v
    rw [hgv', hgv2, herm_add_left, herm_add_right, herm_add_right, herm_inX_perp hv hx,
      herm_inX_perp hv' hx] at e1
    have h1 : herm (Hpk k r) v' v' = 0 := by linear_combination e1
    have e2 := herm_inv hgU v z
    have hgz' : g *ᵥ z = z + (g *ᵥ z - z) := by abel
    rw [hgv2, hgz', herm_add_left, herm_add_right, herm_add_right, herm_perp_inX hv hgz,
      herm_perp_inX hv' hgz] at e2
    have h2 : herm (Hpk k r) v' z = 0 := by linear_combination e2
    exact definite hv' hz hT h1 h2

lemma m_perp {k r : ℕ} {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : Formalism.QuantumDeterminants.WeylGroupFacts.col k r m) {v : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) :
    inX k r (m *ᵥ v - v) := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
  · by_cases hik : i.val ≤ r + k
    · rw [hm i i hik (Or.inr hi), if_pos rfl, one_mul]
    · rw [hv i (by omega), mul_zero]
  · by_cases hjk : j.val ≤ r + k
    · rw [hm i j hjk (Or.inr hi), if_neg (Ne.symm hji), zero_mul]
    · rw [hv j (by omega), mul_zero]

lemma inX_mem {k r : ℕ} {x : Fin (2 * r + k + 1) → ℂ} (hx : inX k r x) : x ∈ Xsp k r := by
  have hx' : x = ∑ a : Fin r, x (eI k r a) • bvec (eI k r a) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
      · have e : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
        rw [if_pos e, ← e]
      · intro a _ ha
        rw [if_neg]
        intro h
        apply ha
        ext
        have := congrArg Fin.val h
        simp only [eI] at this
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hx i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact a.2
  rw [hx']
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end PI.StabSplit.UnipW

namespace PI.StabSplit

open UnipW in
theorem nilpotent_orthogonal_complement : NPerp := by
  intro k r g hg v hv
  obtain ⟨_, h1, h2⟩ := hg
  have hcol : Formalism.QuantumDeterminants.WeylGroupFacts.col k r g := by
    intro i j hj hji
    by_cases hjr : j.val < r
    · have h3 := h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rw [e] at h3
      exact h3
    · exact h2 i j (by omega) hj (by omega)
  have hperp : UnipW.perpX k r v := by
    intro i hi
    have hir : 2 * r + k - i.val < r := by omega
    have h4 := hv ⟨2 * r + k - i.val, hir⟩
    rw [herm_coord, Finset.sum_eq_single (eI k r ⟨2 * r + k - i.val, hir⟩)] at h4
    · have hs : sig k r (eI k r ⟨2 * r + k - i.val, hir⟩) = i := by
        have hc : (eI k r ⟨2 * r + k - i.val, hir⟩).val < r ∨
            r + k < (eI k r ⟨2 * r + k - i.val, hir⟩).val := Or.inl hir
        unfold sig
        rw [if_pos hc]
        apply Fin.ext
        show 2 * r + k - (2 * r + k - i.val) = i.val
        omega
      have hsg : sgn k r (eI k r ⟨2 * r + k - i.val, hir⟩) = 1 := by
        have hc : ¬ (eI k r ⟨2 * r + k - i.val, hir⟩).val = r + k := by
          show ¬ 2 * r + k - i.val = r + k
          omega
        unfold sgn
        rw [if_neg hc]
      rw [hs, hsg] at h4
      simpa [bvec] using h4
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h5 := m_perp hcol hperp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact inX_mem h5

open UnipW in
theorem unipotent_nilpotent_radical : UnipN := by
  intro k r z hzs g hg p hp
  have hz := hzs.1
  have hT := hzs.2
  have hgU : gᴴ * Hpk k r * g = Hpk k r := Sset_UH hg
  obtain ⟨u, hu, m, hm, rfl⟩ := hg
  have hb := Formalism.QuantumDeterminants.WeylGroupFacts.uw_block hu
  have hmc := ((Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m).1 hm).2
  have hzp : perpX k r z := fun i hi => hz i (Or.inr hi)
  have row_out : ∀ i j, (i.val < r ∨ r + k < i.val) → (u * m) i j = m i j := by
    intro i j hi
    rw [mul_apply, Finset.sum_eq_single i]
    · rw [hb.2 i i hi, if_pos rfl, one_mul]
    · intro l _ hl; rw [hb.2 i l hi, if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have xcol : ∀ i j : Fin (2 * r + k + 1), j.val < r → j.val ≤ i.val →
      (u * m) i j = if i = j then 1 else 0 := by
    intro i j hj hij
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [row_out i j hi]; exact hmc i j (by omega) (Or.inl hij)
    · have hne : i ≠ j := by intro h; subst h; omega
      rw [if_neg hne, mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : l.val < r ∨ r + k < l.val
      · rw [hb.1 i l hl, if_neg (by intro h; subst h; omega), zero_mul]
      · rw [hmc l j (by omega) (Or.inr (by omega)), if_neg (by intro h; subst h; omega), mul_zero]
  have u_fix : ∀ x, inX k r x → u *ᵥ x = x := by
    intro x hx
    ext i
    simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hi : i.val < r
      · rw [hb.1 i i (Or.inl hi), if_pos rfl, one_mul]
      · rw [hx i (by omega), mul_zero]
    · intro l _ hl
      by_cases hlr : l.val < r
      · rw [hb.1 i l (Or.inl hlr), if_neg (Ne.symm hl), zero_mul]
      · rw [hx l (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hperp : ∀ v, perpX k r v → perpX k r ((u * m) *ᵥ v) := by
    intro v hv i hi
    have h1 : ((u * m) *ᵥ v) i = (m *ᵥ v) i := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [row_out i j (Or.inr hi)])
    have h2 := m_perp hmc hv i (by omega)
    rw [Pi.sub_apply, sub_eq_zero] at h2
    rw [h1, h2, hv i hi]
  have hgz : inX k r ((u * m) *ᵥ z - z) := by
    have hx := m_perp hmc hzp
    have e : (u * m) *ᵥ z - z = m *ᵥ z - z := by
      rw [← mulVec_mulVec]
      have e2 : m *ᵥ z = z + (m *ᵥ z - z) := by abel
      rw [e2, mulVec_add, hu.2.2, u_fix _ hx]
    rw [e]; exact hx
  have hkey := key hz hT hgU hperp hgz p
  refine (Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).2 ⟨hgU, ?_⟩
  intro i j hj hij
  by_cases hjr : j.val < r
  · exact xcol i j hjr (by omega)
  · have hir : r ≤ i.val := by omega
    have hbp : perpX k r (bvec j) := by
      intro l hl
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; subst h; omega
    have h := hkey (bvec j) hbp (by rw [hp, zero_mulVec]) i hir
    rw [Pi.sub_apply, sub_eq_zero, mulVec_bvec] at h
    have h' : (u * m) i j = bvec j i := h
    rw [h']; simp [bvec, Pi.single_apply]

end PI.StabSplit
