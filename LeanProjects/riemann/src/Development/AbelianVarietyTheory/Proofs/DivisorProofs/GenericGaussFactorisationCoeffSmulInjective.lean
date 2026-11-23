import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef.LduLead

def key (N : ℕ) (v : Fin N × Fin N) : ℕ :=
  if v.1 = v.2 then N - (v.1 : ℕ) else N + 1 + Nat.pair v.1 v.2

theorem key_injective (N : ℕ) : Function.Injective (key N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [key] at h
  split_ifs at h with h1 h2 h2
  · have ha := a.2; have ha' := a'.2
    have : (a : ℕ) = a' := by omega
    ext <;> simp_all [Fin.ext_iff]
  · omega
  · omega
  · have h3 : Nat.pair a b = Nat.pair a' b' := by omega
    rw [Nat.pair_eq_pair] at h3
    ext <;> simp [Fin.ext_iff, h3.1, h3.2]

def Var (N : ℕ) : Type := Fin N × Fin N

instance (N : ℕ) : LinearOrder (Var N) := LinearOrder.lift' (key N) (key_injective N)

instance (N : ℕ) : Finite (Var N) := inferInstanceAs (Finite (Fin N × Fin N))

def ord (N : ℕ) : MonomialOrder (Fin N × Fin N) := MonomialOrder.lex (σ := Var N)

theorem ord_lt_of (N : ℕ) (e f : Fin N × Fin N →₀ ℕ) (i : Fin N × Fin N)
    (h1 : ∀ j, key N j < key N i → e j = f j) (h2 : e i < f i) :
    (ord N).toSyn e < (ord N).toSyn f := by
  have hk : (MonomialOrder.lex (σ := Var N)).toSyn (e : Var N →₀ ℕ) <
      (MonomialOrder.lex (σ := Var N)).toSyn (f : Var N →₀ ℕ) := by
    exact (MonomialOrder.lex_lt_iff (σ := Var N)).2 (Finsupp.Lex.lt_iff.2 ⟨i, fun j hj => h1 j hj, h2⟩)
  exact hk

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

theorem key_lt_diag {N : ℕ} {j : Fin N × Fin N} {d : Fin N} (h : key N j < key N (d, d)) :
    j = (j.1, j.1) ∧ d < j.1 := by
  obtain ⟨x, y⟩ := j
  simp only [key, if_true] at h
  split_ifs at h with hxy
  · subst hxy; refine ⟨rfl, ?_⟩
    rw [Fin.lt_def]; have := d.2; have := x.2; simp at h ⊢; omega
  · omega

def lead (N : ℕ) (v : Fin N × Fin N) : Fin N × Fin N →₀ ℕ :=
  Finsupp.single v 1 + if v.1 = v.2 then 0 else Finsupp.single (min v.1 v.2, min v.1 v.2) 1

theorem lead_ne_zero (N : ℕ) (v : Fin N × Fin N) : lead N v ≠ 0 := by
  intro h
  have := congrArg (fun f => f v) h
  simp [lead] at this

variable (O : Type) [CommRing O] (N : ℕ)

theorem lduHom_X (v : Fin N × Fin N) :
    lduHom O N (X v) = ∑ c : Fin N, lowGen O N v.1 c * X (c, c) * upGen O N c v.2 := by
  rw [lduHom, aeval_X, diagGen, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

variable (O : Type) [CommRing O] (N : ℕ)

theorem lead_apply (v w : Fin N × Fin N) :
    lead N v w = (if v = w then 1 else 0) +
      (if v.1 = v.2 then 0 else if (min v.1 v.2, min v.1 v.2) = w then 1 else 0) := by
  unfold lead
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem entry_lead [Nontrivial O] (a b : Fin N) :
    (ord N).degree (lduHom O N (X (a, b))) = lead N (a, b) ∧
      (ord N).Monic (lduHom O N (X (a, b))) := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = min a b := ⟨_, rfl⟩
  have hda : d ≤ a := hd ▸ min_le_left a b
  have hdb : d ≤ b := hd ▸ min_le_right a b
  have hdab : (d : ℕ) = a ∨ (d : ℕ) = b := by
    rcases le_total a b with h | h
    · left; rw [hd, min_eq_left h]
    · right; rw [hd, min_eq_right h]
  have ht : lowGen O N a d * X (d, d) * upGen O N d b = monomial (lead N (a, b)) 1 := by
    rcases lt_trichotomy a b with h | h | h
    · have e1 : d = a := hd.trans (min_eq_left h.le)
      have e2 : lead N (a, b) = Finsupp.single (a, a) 1 + Finsupp.single (a, b) 1 := by
        simp [lead, h.ne, min_eq_left h.le, add_comm]
      rw [e1, e2]
      simp [lowGen, upGen, h, h.ne, X, monomial_mul]
    · subst h
      have e1 : d = a := hd.trans (min_self a)
      rw [e1]
      simp [lowGen, upGen, lead, X]
    · have e1 : d = b := hd.trans (min_eq_right h.le)
      have e2 : lead N (a, b) = Finsupp.single (a, b) 1 + Finsupp.single (b, b) 1 := by
        simp [lead, h.ne', min_eq_right h.le]
      rw [e1, e2]
      simp [lowGen, upGen, h, h.ne', X, monomial_mul]
  have hpos : 0 < (ord N).toSyn (lead N (a, b)) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero, Ne, (ord N).toSyn_eq_zero_iff]
    exact lead_ne_zero N _
  have hrest : (ord N).toSyn ((ord N).degree (∑ c ∈ Finset.univ.erase d,
      lowGen O N a c * X (c, c) * upGen O N c b)) < (ord N).toSyn (lead N (a, b)) := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro c hc
    have hc' : c ≠ d := Finset.ne_of_mem_erase hc
    by_cases hcd : c < d
    · have hca : c < a := lt_of_lt_of_le hcd hda
      have hcb : c < b := lt_of_lt_of_le hcd hdb
      have hm : lowGen O N a c * X (c, c) * upGen O N c b =
          monomial (Finsupp.single (a, c) 1 + Finsupp.single (c, c) 1 + Finsupp.single (c, b) 1) 1 := by
        simp [lowGen, upGen, hca.ne', hca, hcb.ne, hcb, X, monomial_mul]
      rw [hm]
      have h1 : (d : ℕ) ≤ a := hda
      have h2 : (d : ℕ) ≤ b := hdb
      have h3 : (c : ℕ) < d := hcd
      have h6 : (c : ℕ) < a := hca
      have h7 : (c : ℕ) < b := hcb
      refine lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (ord_lt_of N _ _ (d, d) ?_ ?_)
      · intro j hj
        obtain ⟨hj1, hj2⟩ := key_lt_diag hj
        rw [hj1]
        have h4 : (d : ℕ) < j.1 := hj2
        simp only [lead_apply, ← hd, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]
        split_ifs <;> omega
      · simp only [lead_apply, ← hd, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]
        split_ifs <;> omega
    · have hdc : d < c := lt_of_le_of_ne (not_lt.1 hcd) (Ne.symm hc')
      have hz : lowGen O N a c * X (c, c) * upGen O N c b = 0 := by
        rcases lt_or_ge a c with hac | hca
        · simp [lowGen, hac.ne, not_lt.2 hac.le]
        · have hbc : b < c := by
            rcases min_lt_iff.1 (hd ▸ hdc) with h | h
            · exact absurd hca (not_le.2 h)
            · exact h
          simp [upGen, hbc.ne', not_lt.2 hbc.le]
      rw [hz, MonomialOrder.degree_zero, map_zero]
      exact hpos
  have hsum := lduHom_X O N (a, b)
  dsimp only at hsum
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ d), ht]
  have hm : (ord N).degree (monomial (lead N (a, b)) (1 : O)) = lead N (a, b) := by
    rw [MonomialOrder.degree_monomial]; simp
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt (by rw [hm]; exact hrest), hm]
  · exact MonomialOrder.Monic.add_of_lt MonomialOrder.monic_monomial_one (by rw [hm]; exact hrest)

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

variable (O : Type) [CommRing O] (N : ℕ)

def leadExp (m : Fin N × Fin N →₀ ℕ) : Fin N × Fin N →₀ ℕ := ∑ v, m v • lead N v

theorem leadExp_apply (m : Fin N × Fin N →₀ ℕ) (w : Fin N × Fin N) :
    leadExp N m w = ∑ v, m v * lead N v w := by
  simp [leadExp, Finsupp.finset_sum_apply]

theorem image_monomial_lead [Nontrivial O] (m : Fin N × Fin N →₀ ℕ) :
    (ord N).degree (lduHom O N (monomial m 1)) = leadExp N m ∧
      (ord N).Monic (lduHom O N (monomial m 1)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp [leadExp, MonomialOrder.monic_one]
  | add f g hf hg =>
    have e : monomial (f + g) (1 : O) = monomial f 1 * monomial g 1 := by rw [monomial_mul, one_mul]
    rw [e, map_mul]
    have hle : leadExp N (f + g) = leadExp N f + leadExp N g := by
      simp [leadExp, add_smul, Finset.sum_add_distrib]
    refine ⟨?_, hf.2.mul hg.2⟩
    rw [MonomialOrder.degree_mul_of_isRegular_left (by rw [hf.2.leadingCoeff_eq_one]; exact isRegular_one)
      hg.2.ne_zero, hf.1, hg.1, hle]
  | single v k =>
    rw [← X_pow_eq_monomial, map_pow]
    obtain ⟨a, b⟩ := v
    obtain ⟨h1, h2⟩ := entry_lead O N a b
    have hle : leadExp N (Finsupp.single (a, b) k) = k • lead N (a, b) := by
      rw [leadExp, Finset.sum_eq_single (a, b)]
      · simp
      · intro w _ hw; simp [Finsupp.single_apply, Ne.symm hw]
      · simp
    refine ⟨?_, h2.pow⟩
    rw [MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero (by rw [h2.leadingCoeff_eq_one, one_pow]; exact one_ne_zero),
      h1, hle]

theorem leadExp_injective : Function.Injective (leadExp N) := by
  intro m m' h
  have hw : ∀ w, leadExp N m w = leadExp N m' w := fun w => by rw [h]
  have hoff : ∀ w : Fin N × Fin N, w.1 ≠ w.2 → m w = m' w := by
    intro w hne
    have key : ∀ (n : Fin N × Fin N →₀ ℕ), leadExp N n w = n w := by
      intro n
      rw [leadExp_apply, Finset.sum_eq_single w]
      · have : (min w.1 w.2, min w.1 w.2) ≠ w := fun h' => hne (by rw [← h'])
        rw [lead_apply]; simp [hne, this]
      · intro v _ hv
        rw [lead_apply]
        have : (min v.1 v.2, min v.1 v.2) ≠ w := fun h' => hne (by rw [← h'])
        simp [hv, this]
      · simp
    rw [← key m, ← key m', hw]
  ext w
  by_cases hne : w.1 = w.2
  · have e := hw w
    rw [leadExp_apply, leadExp_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ w),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w)] at e
    have hrest : ∑ v ∈ Finset.univ.erase w, m v * lead N v w = ∑ v ∈ Finset.univ.erase w, m' v * lead N v w := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvw : v ≠ w := Finset.ne_of_mem_erase hv
      by_cases hv' : v.1 = v.2
      · rw [lead_apply]; simp [hvw, hv']
      · rw [hoff v hv']
    rw [hrest, add_left_inj] at e
    have hww : lead N w w = 1 := by rw [lead_apply]; simp [hne]
    simpa [hww] using e
  · exact hoff w hne

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef

open LduLead in

theorem lduHom_coeff_smul_injective : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M),
    (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := by
  intro O _ N M _ _ s c H
  rcases subsingleton_or_nontrivial O with hO | hO
  · intro m _
    rw [← one_smul O (c m), Subsingleton.elim (1 : O) 0, zero_smul]
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨m1, hm1, hc1⟩ := hne
  have hT : (s.filter fun m => c m ≠ 0).Nonempty := ⟨m1, Finset.mem_filter.2 ⟨hm1, hc1⟩⟩
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image _ (fun m => (ord N).toSyn (leadExp N m)) hT
  rw [Finset.mem_filter] at hm0
  have e := H (leadExp N m0)
  rw [Finset.sum_eq_single m0] at e
  · obtain ⟨h1, h2⟩ := image_monomial_lead O N m0
    rw [← h1, h2.coeff_degree, one_smul] at e
    exact hm0.2 e
  · intro m hm hmm
    by_cases hcm : c m = 0
    · rw [hcm, smul_zero]
    · have hle := hmax m (Finset.mem_filter.2 ⟨hm, hcm⟩)
      have hlt : (ord N).toSyn (leadExp N m) < (ord N).toSyn (leadExp N m0) :=
        lt_of_le_of_ne hle fun h' => hmm (leadExp_injective N ((ord N).toSyn.injective h'))
      rw [MonomialOrder.coeff_eq_zero_of_lt (by rw [(image_monomial_lead O N m).1]; exact hlt), zero_smul]
  · intro h; exact absurd hm0.1 h

end GlobalTheory.GenCoef

end
