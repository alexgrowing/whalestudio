import Formalism.BranchSandwichDivisors.StatementW
import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL

noncomputable section

namespace Formalism.BranchingDeterminantCap

lemma bs_fock_smul_left {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_left]

lemma bs_fock_smul_right {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_right]

lemma bs_zScale_prod (n : ℕ) (t : ℝ) (e : Fin (n + 1) → ℕ) :
    ∏ a, (if a = Fin.last n then (t : ℂ) else 1) ^ e a = (t : ℂ) ^ e (Fin.last n) := by
  rw [Finset.prod_eq_single (Fin.last n)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem branch_scale_formula : BranchScale := by
  intro n k d t F hF
  have h1 : rowAct ℂ (zScale n t) F = ((t : ℂ) ^ d) • F := by
    ext m
    rw [zScale, ldrow_coeff_rowAct_diag, bs_zScale_prod, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ F.support
    · rw [hF m hm, mul_comm]
    · rw [notMem_support_iff.mp hm]; simp
  refine ⟨h1, ?_⟩
  rw [h1, bs_fock_smul_left, bs_fock_smul_right]
  have : star ((t : ℂ) ^ d) = (t : ℂ) ^ d := by simp
  rw [this, two_mul, pow_add]; ring

lemma bs_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (hf : f ∈ weyl ℚ r n hn ν) : map (algebraMap ℚ ℂ) f ∈ weyl ℂ r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

lemma bs_dual_le_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    dualWeyl ℂ r n ν ≤ weyl ℂ r n hn ν := by
  rw [standardMonomialSpanDomain ℂ r n ν, Submodule.span_le]
  rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
  rw [← ldlat_map_bidet (algebraMap ℚ ℂ)]
  apply bs_map_weyl
  rw [weylEqNablaQ r n hn ν hν, ← hsh]
  exact bidetMem ℚ r n K sz hsz I

lemma bs_dom {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : f ∈ dualWeyl ℂ r n ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin r, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ r n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance ℂ r n K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

lemma bs_abel (n : ℕ) (x : Fin n → ℤ) :
    ∑ a, (a.val : ℤ) * x a =
      ∑ k ∈ Finset.range n, ((∑ a, x a) - ∑ a : Fin n with a.val < k + 1, x a) := by
  have h1 : ∀ a : Fin n, (a.val : ℤ) = ∑ k ∈ Finset.range n, if k < a.val then (1 : ℤ) else 0 := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.range n).filter (fun k => k < a.val) = Finset.range a.val := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      have := a.isLt
      omega
    rw [this, Finset.card_range]
  calc ∑ a, (a.val : ℤ) * x a
      = ∑ a : Fin n, ∑ k ∈ Finset.range n, (if k < a.val then x a else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [h1 a]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k ∈ Finset.range n, ∑ a : Fin n, (if k < a.val then x a else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : k < a.val
        · rw [if_pos h, if_neg (by omega)]; ring
        · rw [if_neg h, if_pos (by omega)]; ring

lemma bs_height_le (n : ℕ) (x y : Fin n → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin n with a.val < k, x a) ≤ ∑ a : Fin n with a.val < k, y a)
    (h2 : ∑ a, x a = ∑ a, y a) :
    ∑ a : Fin n, (a.val : ℤ) * (y a : ℤ) ≤ ∑ a : Fin n, (a.val : ℤ) * (x a : ℤ) := by
  rw [bs_abel, bs_abel]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 := h1 (k + 1)
  have e1' : (∑ a : Fin n with a.val < k + 1, (x a : ℤ)) ≤ ∑ a : Fin n with a.val < k + 1, (y a : ℤ) := by
    exact_mod_cast e1
  have e2' : (∑ a, (x a : ℤ)) = ∑ a, (y a : ℤ) := by exact_mod_cast h2
  linarith

lemma bs_hwspace {n : ℕ} (sg : Fin n → ℕ) (hsg : Antitone sg) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : q ∈ dualWeyl ℂ n n sg) (hqw : IsWeightedHomogeneous (rowW n n) q sg) :
    ∃ c : ℂ, q = c • hw ℂ le_rfl sg := by
  apply hwLine ℂ n n le_rfl sg hsg q hq
  intro a b hab k hk
  by_contra hne
  have hmem := rowDivStable ℂ n n sg a b k q hq
  have hht : IsWeightedHomogeneous (lhwinHt n n) q (∑ a : Fin n, (a.val : ℤ) * (sg a : ℤ)) := by
    intro d hd
    rw [lhwin_weight_ht, hqw hd]
  have hsh := lhwin_rowDiv_shift ℂ _ a b k q hht
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
  have e := hsh hd
  rw [lhwin_weight_ht] at e
  simp only [ldrow_weight_rowW] at e
  have dom := bs_dom sg _ hmem d (mem_support_iff.mpr hd)
  have hle := bs_height_le n (rowDeg d) sg dom.1 dom.2
  have hab' : (a.val : ℤ) - b.val ≤ -1 := by
    have : a.val < b.val := hab
    omega
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

structure BsForm {n : ℕ} (sg : Fin n → ℕ)
    (D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ) : Prop where
  addl : ∀ p p' q, D (p + p') q = D p q + D p' q
  smull : ∀ (c : ℂ) p q, D (c • p) q = c * D p q
  addr : ∀ p q q', D p (q + q') = D p q + D p q'
  smulr : ∀ (c : ℂ) p q, D p (c • q) = star c * D p q
  adj : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg,
    D (rowAct ℂ g p) q = D p (rowAct ℂ g.conjTranspose q)

namespace BsForm

variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}

lemma zerol (H : BsForm sg D) (q) : D 0 q = 0 := by
  have := H.smull 0 0 q
  simpa using this

lemma zeror (H : BsForm sg D) (p) : D p 0 = 0 := by
  have := H.smulr 0 p 0
  simpa using this

lemma suml (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (q) :
    D (∑ i ∈ s, g i) q = ∑ i ∈ s, D (g i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.zerol]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.addl, ih]

lemma sumr (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (p) :
    D p (∑ i ∈ s, g i) = ∑ i ∈ s, D p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.zeror]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.addr, ih]

lemma hw_weight (H : BsForm sg D) (hsg : Antitone sg) (μ : Fin n → ℕ) (hμ : μ ≠ sg)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg)
    (hqw : IsWeightedHomogeneous (rowW n n) q μ) : D (hw ℂ le_rfl sg) q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin n → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin n → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have hnu : rowNu (r := n) sg = sg := by
    funext b
    simp [rowNu]
  have hhw : IsWeightedHomogeneous (rowW n n) (hw ℂ le_rfl sg) sg := by
    have := hwRowWeight ℂ n n le_rfl sg hsg
    rwa [hnu] at this
  have hconj : (Matrix.diagonal t).conjTranspose = Matrix.diagonal t := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext b
    by_cases hb : b = a <;> simp [t, hb]
  have e := H.adj (Matrix.diagonal t) _ (hwMem ℂ n n le_rfl sg hsg) q hq
  rw [hconj, rowActDiagWeight ℂ n n t sg _ hhw, rowActDiagWeight ℂ n n t μ _ hqw, hprod, hprod,
    H.smull, H.smulr] at e
  have hstar : star ((2 : ℂ) ^ μ a) = 2 ^ μ a := by simp
  rw [hstar] at e
  have hne : (2 : ℂ) ^ sg a - 2 ^ μ a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ sg a = 2 ^ μ a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h').symm
  have : ((2 : ℂ) ^ sg a - 2 ^ μ a) * D (hw ℂ le_rfl sg) q = 0 := by rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

lemma hw_rad (H : BsForm sg D) (hsg : Antitone sg) (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg) : D (hw ℂ le_rfl sg) q = 0 := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW n n) q
  have hsum := sum_weightedHomogeneousComponent (rowW n n) q
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, H.sumr]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hmem := dualWeylRowGraded ℂ n n sg μ q hq
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW n n) μ q
  by_cases hμ : μ = sg
  · subst hμ
    obtain ⟨c, hc⟩ := bs_hwspace μ hsg _ hmem hw'
    rw [hc, H.smulr, h0, mul_zero]
  · exact H.hw_weight hsg μ hμ _ hmem hw'

lemma rad_rowDiv (H : BsForm sg D) (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ dualWeyl ℂ n n sg)
    (h0 : ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0) (a b : Fin n) (k : ℕ) :
    ∀ q ∈ dualWeyl ℂ n n sg, D (rowDiv ℂ a b k p) q = 0 := by
  intro q hq
  set N := (rowGen ℂ a b p).natDegree + k + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (D (rowDiv ℂ a b i p) q) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := H.adj (lfockq_mat a b c) p hp q hq
    rw [h0 _ (dualWeylRowStable ℂ n n sg _ q hq), ← lfockq_eval_rowGen, lfockq_eval_C _ N h1,
      H.suml] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, H.smull, mul_comm]
    rfl
  have := congrArg (fun p => Polynomial.coeff p k) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem eq_zero (H : BsForm sg D) (hsg : Antitone sg)
    (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0) :
    ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0 := by
  have W : ∀ w : List (Fin n × Fin n × ℕ), applyWord ℂ w (hw ℂ le_rfl sg) ∈ dualWeyl ℂ n n sg ∧
      ∀ q ∈ dualWeyl ℂ n n sg, D (applyWord ℂ w (hw ℂ le_rfl sg)) q = 0 := by
    intro w
    induction w with
    | nil => exact ⟨hwMem ℂ n n le_rfl sg hsg, H.hw_rad hsg h0⟩
    | cons x w ih =>
      rw [applyWord_cons]
      exact ⟨rowDivStable ℂ n n sg _ _ _ _ ih.1, H.rad_rowDiv _ ih.1 ih.2 _ _ _⟩
  intro p hp q hq
  have key : ∀ p ∈ weyl ℂ n n le_rfl sg, D p q = 0 := by
    intro p hp'
    unfold weyl at hp'
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact (W w).2 q hq
    | zero => exact H.zerol q
    | add x y _ _ hx hy => rw [H.addl, hx, hy, add_zero]
    | smul c x _ hx => rw [H.smull, hx, mul_zero]
  exact key p (bs_dual_le_weyl le_rfl sg hsg hp)

end BsForm

lemma bs_extM_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (extM ℂ g).conjTranspose = extM ℂ g.conjTranspose := by
  ext a b
  simp only [Matrix.conjTranspose_apply, extM, Matrix.of_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]
    by_cases e : a = b
    · subst e; simp
    · rw [if_neg e, if_neg (Ne.symm e)]; simp

theorem branch_isometry : BranchIsometry := by
  intro n sg hsg io heq f h hh
  obtain ⟨io', hio'⟩ := LinearMap.exists_extend io
  have hio : ∀ p (hp : p ∈ dualWeyl ℂ n n sg), io' p = io ⟨p, hp⟩ := by
    intro p hp
    rw [← hio']
    rfl
  have hact : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ dualWeyl ℂ n n sg,
      io' (rowAct ℂ g p) = rowAct ℂ (extM ℂ g) (io' p) := by
    intro g p hp
    rw [hio _ (dualWeylRowStable ℂ n n sg g p hp), hio p hp]
    exact heq g ⟨p, hp⟩ ⟨_, dualWeylRowStable ℂ n n sg g p hp⟩ rfl
  let D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ := fun p q =>
    fockF (io' p) (io' q) * fockF (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) -
      fockF (io' (hw ℂ le_rfl sg)) (io' (hw ℂ le_rfl sg)) * fockF p q
  have H : BsForm sg D := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p p' q
      simp only [D, map_add, fischerInner_add_left]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_left]; ring
    · intro p q q'
      simp only [D, map_add, fischerInner_add_right]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_right]; ring
    · intro g p hp q hq
      simp only [D]
      rw [hact g p hp, hact _ q hq, fockRowAdj (n + 1) n, fockRowAdj n n, bs_extM_conj]
  have h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0 := by
    simp only [D]; ring
  have e := H.eq_zero hsg h0 f f.2 f f.2
  simp only [D] at e
  have e1 : io' (f : MvPolynomial (Fin n × Fin n) ℂ) = io f := hio _ f.2
  have e2 : io' (hw ℂ le_rfl sg) = io h := by
    rw [← hh]; exact hio _ h.2
  rw [e1, e2] at e
  rw [hh]
  exact sub_eq_zero.mp e

lemma bs_antitone {n : ℕ} (lam sg : Fin n → ℕ) (h : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone sg := by
  have step : ∀ (a b : Fin n), b.val = a.val + 1 → sg b ≤ sg a := by
    intro a b hab
    have h1 := (h a).2
    have h2 := (h b).1
    have e : (a.succ : Fin (n + 1)) = b.castSucc := by
      ext; simp [hab]
    rw [e] at h1
    have : (sg b : ℤ) ≤ sg a := le_trans h2 h1
    exact_mod_cast this
  have all : ∀ (k : ℕ) (a b : Fin n), b.val = a.val + k → sg b ≤ sg a := by
    intro k
    induction k with
    | zero =>
      intro a b hab
      have : a = b := by ext; omega
      rw [this]
    | succ k ih =>
      intro a b hab
      have hlt : a.val + k < n := by have := b.isLt; omega
      exact le_trans (step ⟨a.val + k, hlt⟩ b (by simp; omega)) (ih a ⟨a.val + k, hlt⟩ rfl)
  intro a b hab
  exact all (b.val - a.val) a b (by have : a.val ≤ b.val := hab; omega)

lemma bs_zScale_hw (n : ℕ) (lam : Fin n → ℕ) (t : ℝ) :
    rowAct ℂ (zScale n t) (hw ℂ (Nat.le_succ n) lam) = hw ℂ (Nat.le_succ n) lam := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow]
  congr 1
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  have hne : Fin.castLE (by omega : s.val + 1 ≤ n + 1) p ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have h1 := p.isLt
    have h2 := s.isLt
    omega
  simp [zScale, ldrow_rowAct_diag_eq, hne]

theorem branch_norm_trace : BranchNormT := by
  intro n lam sg t hint io heq hhw hdeg
  refine ⟨bs_zScale_hw n lam t, fun f => ?_⟩
  have hsg := bs_antitone lam sg hint
  let h : ↥(dualWeyl ℂ n n sg) := ⟨hw ℂ le_rfl sg, hwMem ℂ n n le_rfl sg hsg⟩
  have e1 := (branch_scale_formula n n _ t (io f) (hdeg f)).2
  have e2 := branch_isometry n sg hsg io heq f h rfl
  have e3 := hhw h rfl
  rw [e3, bs_fock_smul_left, bs_fock_smul_right] at e2
  have hstar : star (((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ)) =
      ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ) := by simp
  rw [hstar] at e2
  rw [e1, mul_assoc, e2]
  ring

end Formalism.BranchingDeterminantCap
