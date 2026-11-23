import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreAndCapelli
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

noncomputable section

namespace GlobalTheory.MinorGerm

section General
variable {C : Type} [Field C] {σ : Type}

def Low (α : σ →₀ ℕ) (g : MvPowerSeries σ C) : Prop :=
  MvPowerSeries.coeff α g = 1 ∧
    ∀ m : σ →₀ ℕ, m.degree ≤ α.degree → m ≠ α → MvPowerSeries.coeff m g = 0

theorem low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C) := by
  classical
  refine ⟨by simp, fun m _ hm => ?_⟩
  rw [MvPowerSeries.coeff_one, if_neg hm]

theorem Low.term {α β : σ →₀ ℕ} {g h : MvPowerSeries σ C} (hg : Low α g) (hh : Low β h)
    (a b : σ →₀ ℕ) (hd : a.degree + b.degree ≤ α.degree + β.degree) (hne : (a, b) ≠ (α, β)) :
    MvPowerSeries.coeff a g * MvPowerSeries.coeff b h = 0 := by
  classical
  by_cases ha : a.degree ≤ α.degree ∧ a ≠ α
  · rw [hg.2 a ha.1 ha.2, zero_mul]
  by_cases hb : b.degree ≤ β.degree ∧ b ≠ β
  · rw [hh.2 b hb.1 hb.2, mul_zero]
  exfalso
  push_neg at ha hb
  by_cases ha' : a = α
  · by_cases hb' : b = β
    · exact hne (by rw [ha', hb'])
    · have : ¬ b.degree ≤ β.degree := fun h => hb' (hb h)
      rw [ha'] at hd
      omega
  · have : ¬ a.degree ≤ α.degree := fun h => ha' (ha h)
    by_cases hb' : b = β
    · rw [hb'] at hd
      omega
    · have : ¬ b.degree ≤ β.degree := fun h => hb' (hb h)
      omega

theorem Low.mul {α β : σ →₀ ℕ} {g h : MvPowerSeries σ C} (hg : Low α g) (hh : Low β h) :
    Low (α + β) (g * h) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (α, β)]
    · rw [hg.1, hh.1, mul_one]
    · intro q hq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      apply hg.term hh
      · have h := congrArg Finsupp.degree hq
        rw [map_add, map_add] at h
        omega
      · exact hne
    · intro h
      exact (h (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl)).elim
  · intro m hm hne
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    apply hg.term hh
    · have h := congrArg Finsupp.degree hq
      rw [map_add] at h hm
      omega
    · intro h
      apply hne
      rw [Prod.mk.injEq] at h
      rw [← hq, h.1, h.2]

theorem low_prod {ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (g : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, Low (α i) (g i)) : Low (∑ i ∈ s, α i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem Low.pow {α : σ →₀ ℕ} {g : MvPowerSeries σ C} (hg : Low α g) (n : ℕ) :
    Low (n • α) (g ^ n) := by
  classical
  induction n with
  | zero => simpa using (low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C))
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hg

theorem low_tangent {t : σ → MvPowerSeries σ C} (ht : TangentId t) (x : σ) (n : ℕ) :
    Low (Finsupp.single x n) (t x ^ n) := by
  classical
  have h1 : Low (Finsupp.single x 1) (t x) := by
    refine ⟨?_, ?_⟩
    · rw [ht x _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X, if_pos rfl]
    · intro m hm hne
      rw [Finsupp.degree_single] at hm
      rw [ht x m hm, MvPowerSeries.coeff_X, if_neg hne]
  have h2 := h1.pow n
  rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at h2

def kill (p : σ → Prop) [DecidablePred p] : MvPolynomial σ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun x => if p x then MvPolynomial.X x else 0

theorem coeff_kill (p : σ → Prop) [DecidablePred p] (m : σ →₀ ℕ) (hm : ∀ x ∈ m.support, p x)
    (P : MvPolynomial σ C) : MvPolynomial.coeff m (kill p P) = MvPolynomial.coeff m P := by
  classical
  refine MvPolynomial.induction_on' P (fun u a => ?_) (fun P Q hP hQ => ?_)
  · unfold kill
    rw [MvPolynomial.aeval_monomial]
    by_cases hu : ∀ x ∈ u.support, p x
    · have h : (u.prod fun i k => (if p i then MvPolynomial.X i else 0 : MvPolynomial σ C) ^ k) =
          u.prod fun i k => MvPolynomial.X i ^ k := by
        apply Finset.prod_congr rfl
        intro x hx
        dsimp only
        rw [if_pos (hu x hx)]
      rw [h, MvPolynomial.algebraMap_eq, ← MvPolynomial.monomial_eq]
    · push_neg at hu
      obtain ⟨x, hx, hpx⟩ := hu
      have hz : (u.prod fun i k => (if p i then MvPolynomial.X i else 0 : MvPolynomial σ C) ^ k) = 0 := by
        rw [Finsupp.prod]
        apply Finset.prod_eq_zero hx
        rw [if_neg hpx]
        exact zero_pow (Finsupp.mem_support_iff.1 hx)
      rw [hz, mul_zero, MvPolynomial.coeff_zero, MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      exact hpx (hm x hx)
  · rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ]

def Lead (p : σ → Prop) [DecidablePred p] (α : σ →₀ ℕ) (P : MvPolynomial σ C) : Prop :=
  kill p P = MvPolynomial.monomial α 1 ∧ P.IsHomogeneous α.degree ∧ ∀ x ∈ α.support, p x

variable {p : σ → Prop} [DecidablePred p]

theorem lead_one : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C) := by
  classical
  refine ⟨by simp, by simpa using MvPolynomial.isHomogeneous_one σ C, by simp⟩

theorem Lead.mul {α β : σ →₀ ℕ} {P Q : MvPolynomial σ C} (hP : Lead p α P) (hQ : Lead p β Q) :
    Lead p (α + β) (P * Q) := by
  classical
  obtain ⟨hkP, hhP, hsP⟩ := hP
  obtain ⟨hkQ, hhQ, hsQ⟩ := hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hkP, hkQ, MvPolynomial.monomial_mul, mul_one]
  · rw [map_add]
    exact hhP.mul hhQ
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hsP x h
    · exact hsQ x h

theorem lead_prod {ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (P : ι → MvPolynomial σ C)
    (h : ∀ i ∈ s, Lead p (α i) (P i)) : Lead p (∑ i ∈ s, α i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lead_one (p := p) : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem Lead.pow {α : σ →₀ ℕ} {P : MvPolynomial σ C} (hP : Lead p α P) (n : ℕ) :
    Lead p (n • α) (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (lead_one (p := p) : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C))
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hP

theorem jet_eq {α : σ →₀ ℕ} {P : MvPolynomial σ C} {g : MvPowerSeries σ C} (hP : Lead p α P)
    (hg : Low α g) : jetAt0 P g = (mfact α : C) := by
  classical
  obtain ⟨hk, hh, hs⟩ := hP
  obtain ⟨h1, h0⟩ := hg
  have hcoef : MvPolynomial.coeff α P = 1 := by
    rw [← coeff_kill p α hs P, hk, MvPolynomial.coeff_monomial, if_pos rfl]
  unfold jetAt0
  rw [Finset.sum_eq_single α]
  · rw [hcoef, h1]
    ring
  · intro m hm hne
    have hdeg : m.degree = α.degree := by
      by_contra hd
      exact (MvPolynomial.mem_support_iff.1 hm) (hh.coeff_eq_zero hd)
    rw [h0 m hdeg.le hne, mul_zero]
  · intro hα
    exact absurd (MvPolynomial.mem_support_iff.2 (by rw [hcoef]; exact one_ne_zero)) hα

theorem lead_det {k : ℕ} (w : Fin k → Fin k → σ) (hw : ∀ b c, p (w b c) ↔ b = c) :
    Lead p (∑ b, Finsupp.single (w b b) 1)
      (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [AlgHom.map_det]
    have hM : (kill p).mapMatrix (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)) =
        Matrix.diagonal fun b => MvPolynomial.X (w b b) := by
      ext b c
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply, kill,
        MvPolynomial.aeval_X]
      by_cases hbc : b = c
      · subst hbc
        simp [(hw b b).2 rfl]
      · simp [hbc, (hw b c).not.2 hbc]
    rw [hM, Matrix.det_diagonal, MvPolynomial.monomial_sum_one]
    rfl
  · have hdeg : (∑ b : Fin k, Finsupp.single (w b b) 1).degree = k := by
      rw [map_sum]
      simp [Finsupp.degree_single]
    rw [hdeg, Matrix.det_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro s _
    have hprod : MvPolynomial.IsHomogeneous (∏ i, (Matrix.of fun b c : Fin k =>
        (MvPolynomial.X (w b c) : MvPolynomial σ C)) (s i) i) k := by
      have h := MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun i => (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)) (s i) i)
        (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X _ _)
      simpa using h
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · rw [h, one_smul]
      exact hprod
    · rw [h, Units.neg_smul, one_smul]
      exact hprod.neg
  · intro x hx
    obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hx)
    have hx' := Finsupp.support_single_subset hb
    rw [Finset.mem_singleton] at hx'
    rw [hx']
    exact (hw b b).2 rfl

end General

section Diagonal
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}

def dgOne (j : Fin N × Fin N' → σ) (ρ n : ℕ) : σ →₀ ℕ :=
  if h : ρ < N ∧ ρ < N' then Finsupp.single (j (⟨ρ, h.1⟩, ⟨ρ, h.2⟩)) n else 0

def dg (j : Fin N × Fin N' → σ) (f : ℕ → ℕ) : σ →₀ ℕ := ∑ ρ ∈ Finset.range N, dgOne j ρ (f ρ)

theorem dgOne_eq_smul (j : Fin N × Fin N' → σ) (ρ n : ℕ) : dgOne j ρ n = n • dgOne j ρ 1 := by
  classical
  unfold dgOne
  split_ifs <;> simp [Finsupp.smul_single]

theorem monAl_eq_zero (e : ℕ → ℕ) {ρ : ℕ} (h : ¬ ρ < N') : monAl N N' e ρ = 0 := by
  classical
  unfold monAl
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

theorem monAl_eq (e : ℕ → ℕ) (ρ : ℕ) :
    monAl N N' e ρ = ∑ k ∈ Finset.Icc 1 (min N N'), if ρ < k then e k else 0 := by
  classical
  unfold monAl
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_Icc, Finset.mem_filter]
  omega

theorem sum_range_ite {M : Type} [AddCommMonoid M] {k : ℕ} (hk : k ≤ N) (F : ℕ → M) :
    ∑ ρ ∈ Finset.range N, (if ρ < k then F ρ else 0) = ∑ ρ ∈ Finset.range k, F ρ := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem dg_monAl (j : Fin N × Fin N' → σ) (e : ℕ → ℕ) :
    dg j (monAl N N' e) =
      ∑ k ∈ Finset.Icc 1 (min N N'), e k • ∑ ρ ∈ Finset.range k, dgOne j ρ 1 := by
  classical
  unfold dg
  have h : ∀ ρ, dgOne j ρ (monAl N N' e ρ) =
      ∑ k ∈ Finset.Icc 1 (min N N'), if ρ < k then e k • dgOne j ρ 1 else 0 := by
    intro ρ
    rw [dgOne_eq_smul, monAl_eq, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [sum_range_ite (by omega : k ≤ N) (fun ρ => e k • dgOne j ρ 1), Finset.smul_sum]

theorem sum_monAl (e : ℕ → ℕ) : ∑ ρ : Fin N, monAl N N' e ρ.val = monDeg N N' e := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun ρ => monAl N N' e ρ) N]
  simp only [monAl_eq]
  rw [Finset.sum_comm]
  unfold monDeg
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [sum_range_ite (by omega : k ≤ N) (fun _ => e k), Finset.sum_const, Finset.card_range, smul_eq_mul]

variable {p : σ → Prop} [DecidablePred p]

theorem lead_minor (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val) {k : ℕ}
    (hk : k ≤ min N N') :
    Lead p (∑ ρ ∈ Finset.range k, dgOne j ρ 1) (MvPolynomial.rename j (minorK C N N' k)) := by
  classical
  have h1 : k ≤ N := le_trans hk (min_le_left _ _)
  have h2 : k ≤ N' := le_trans hk (min_le_right _ _)
  have hw : ∀ b c : Fin k, p (j (Fin.castLE h1 b, Fin.castLE h2 c)) ↔ b = c := by
    intro b c
    rw [hj, Fin.val_castLE, Fin.val_castLE, Fin.val_inj]
  have hL := lead_det (C := C) (p := p) (fun b c : Fin k => j (Fin.castLE h1 b, Fin.castLE h2 c)) hw
  have hpoly : MvPolynomial.rename j (minorK C N N' k) = (Matrix.of fun b c : Fin k =>
      (MvPolynomial.X (j (Fin.castLE h1 b, Fin.castLE h2 c)) : MvPolynomial σ C)).det := by
    unfold minorK
    rw [dif_pos ⟨h1, h2⟩, AlgHom.map_det]
    congr 1
    ext b c
    simp [MvPolynomial.rename_X]
  have hexp : ∑ ρ ∈ Finset.range k, dgOne j ρ 1 =
      ∑ b : Fin k, Finsupp.single (j (Fin.castLE h1 b, Fin.castLE h2 b)) 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun ρ => dgOne j ρ 1) k]
    apply Finset.sum_congr rfl
    intro b _
    unfold dgOne
    rw [dif_pos ⟨lt_of_lt_of_le b.isLt h1, lt_of_lt_of_le b.isLt h2⟩]
    rfl
  rw [hpoly, hexp]
  exact hL

theorem lead_monP (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val)
    (e : ℕ → ℕ) :
    Lead p (dg j (monAl N N' e)) (MvPolynomial.rename j (monP C N N' e)) := by
  classical
  unfold monP
  rw [map_prod]
  simp_rw [map_pow]
  rw [dg_monAl]
  apply lead_prod
  intro k hk
  exact (lead_minor j hj (Finset.mem_Icc.1 hk).2).pow (e k)

theorem low_monG (j : Fin N × Fin N' → σ) {t : σ → MvPowerSeries σ C} (ht : TangentId t)
    (e : ℕ → ℕ) : Low (dg j (monAl N N' e)) (monG N N' e fun x => t (j x)) := by
  classical
  unfold monG dg
  rw [← Fin.sum_univ_eq_sum_range (fun ρ => dgOne j ρ (monAl N N' e ρ)) N]
  apply low_prod
  intro ρ _
  unfold dgOne
  by_cases h : ρ.val < N'
  · rw [dif_pos h, dif_pos ⟨ρ.isLt, h⟩]
    exact low_tangent ht (j (ρ, ⟨ρ, h⟩)) _
  · rw [dif_neg h, dif_neg (fun hh => h hh.2)]
    exact low_one

theorem dg_apply (j : Fin N × Fin N' → σ) (hj : Function.Injective j) (f : ℕ → ℕ)
    (b : Fin N) (c : Fin N') : dg j f (j (b, c)) = if b.val = c.val then f b.val else 0 := by
  classical
  unfold dg
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b.val]
  · unfold dgOne
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, dif_pos ⟨b.isLt, by rw [hbc]; exact c.isLt⟩, Finsupp.single_apply,
        if_pos (by congr 1; exact Prod.ext (Fin.ext rfl) (Fin.ext hbc))]
    · rw [if_neg hbc]
      split_ifs with h
      · rw [Finsupp.single_apply, if_neg]
        intro he
        have h' := congrArg (fun x => x.2.val) (hj he)
        exact hbc (by simpa using h')
      · rfl
  · intro ρ _ hρ
    unfold dgOne
    split_ifs with h
    · rw [Finsupp.single_apply, if_neg]
      intro he
      have h' := congrArg (fun x => x.1.val) (hj he)
      exact hρ (by simpa using h')
    · rfl
  · intro hb
    exact absurd (Finset.mem_range.2 b.isLt) hb

theorem dg_apply_of_notMem (j : Fin N × Fin N' → σ) (f : ℕ → ℕ) (x : σ) (hx : ∀ y, x ≠ j y) :
    dg j f x = 0 := by
  classical
  unfold dg
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  unfold dgOne
  split_ifs
  · rw [Finsupp.single_apply, if_neg (fun h => hx _ h.symm)]
  · rfl

theorem prod_factorial_diag (e : ℕ → ℕ) :
    ∏ x : Fin N × Fin N', (if x.1.val = x.2.val then monAl N N' e x.1.val else 0).factorial =
      ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial := by
  classical
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro b _
  by_cases hb : b.val < N'
  · rw [Finset.prod_eq_single ⟨b.val, hb⟩]
    · simp
    · intro c _ hc
      rw [if_neg, Nat.factorial_zero]
      intro h
      exact hc (Fin.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [monAl_eq_zero e hb, Nat.factorial_zero]
    apply Finset.prod_eq_one
    intro c _
    rw [if_neg, Nat.factorial_zero]
    intro h
    have h' : b.val = c.val := h
    exact hb (by rw [h']; exact c.isLt)

end Diagonal

section Valuation
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem val_nat_nonneg (n : ℕ) : 0 ≤ v (n : C) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact le_trans (le_min ih (AddValuation.map_one v).ge) (AddValuation.map_add v _ _)

theorem val_coprime {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : ¬ l ∣ n) :
    v (n : C) = 0 := by
  classical
  have hpos := val_nat_nonneg v n
  have hcop : Nat.Coprime n l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hl.one_lt
  have hq : n * a = l * (n * a / l) + 1 := by
    have h := Nat.div_add_mod (n * a) l
    rw [ha] at h
    exact h.symm
  have h01 : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  by_contra hne
  have hlt : 0 < v (n : C) := lt_of_le_of_ne hpos (Ne.symm hne)
  have h1 : 0 < v ((n : C) * a) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_nat_nonneg v a))
  have h2 : 0 < v ((l : C) * ((n * a / l : ℕ) : C)) := by
    rw [AddValuation.map_mul, hv]
    exact lt_of_lt_of_le h01 (le_add_of_nonneg_right (val_nat_nonneg v _))
  have hC : (1 : C) = (n : C) * a - (l : C) * ((n * a / l : ℕ) : C) := by
    have h := congrArg (fun x : ℕ => (x : C)) hq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    rw [h]
    ring
  have h3 := AddValuation.map_sub v ((n : C) * a) ((l : C) * ((n * a / l : ℕ) : C))
  rw [← hC, AddValuation.map_one] at h3
  exact absurd h3 (not_le.2 (lt_min h1 h2))

theorem val_nat {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : n ≠ 0) :
    v (n : C) = (((padicValNat l n : ℕ) : ℝ) : WithTop ℝ) := by
  classical
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hfact := Fact.mk hl
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, AddValuation.map_mul,
    AddValuation.map_pow, hv, val_coprime v hl hv hm, add_zero, ← WithTop.coe_one, ← WithTop.coe_nsmul,
    nsmul_eq_mul, mul_one]

end Valuation

theorem mon_one_type : MON := by
  classical
  intro C _ _ N N' e t ht
  classical
  have hL := lead_monP (C := C) (p := fun x : Fin N × Fin N' => x.1.val = x.2.val) id (fun b c => Iff.rfl) e
  have hG := low_monG (C := C) (N := N) (N' := N') id ht e
  simp only [MvPolynomial.rename_id, AlgHom.id_apply] at hL
  have hjet := jet_eq hL hG
  have hm2 : mfact (dg (id : Fin N × Fin N' → Fin N × Fin N') (monAl N N' e)) =
      ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial := by
    rw [GlobalTheory.LegendreFacts.mfact_eq_prod, ← prod_factorial_diag e]
    apply Finset.prod_congr rfl
    intro x _
    obtain ⟨b, c⟩ := x
    exact congrArg Nat.factorial (dg_apply id Function.injective_id _ b c)
  refine ⟨?_, sum_monAl e, ?_⟩
  · rw [← hm2]
    exact hjet
  · intro v l hl hv
    set M := ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial with hM
    have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun ρ _ => Nat.factorial_ne_zero _)
    refine ⟨?_, ?_⟩
    · rw [val_nat v hl hv hM0, WithTop.coe_le_coe]
      let A : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun ρ => monAl N N' e ρ.val)
      have hA1 : mfact A = M := by
        rw [GlobalTheory.LegendreFacts.mfact_eq_prod]
        rfl
      have hA2 : A.degree = monDeg N N' e := by
        rw [GlobalTheory.LegendreFacts.degree_eq_sum', ← sum_monAl e]
        rfl
      by_cases hd : 1 ≤ A.degree
      · have h := ((GlobalTheory.LegendreFacts.legendre_facts l hl).2.2.1 (Fin N) A hd).2
        rw [hA1, hA2] at h
        exact h
      · have hd0 : monDeg N N' e = 0 := by omega
        have hall : ∀ ρ : Fin N, monAl N N' e ρ.val = 0 := by
          intro ρ
          have h := sum_monAl (N := N) (N' := N') e
          rw [hd0] at h
          exact (Finset.sum_eq_zero_iff.1 h) ρ (Finset.mem_univ _)
        have hM1 : M = 1 := by
          rw [hM]
          simp [hall]
        rw [hM1, hd0]
        simp
    · intro hlt
      apply val_coprime v hl hv
      rw [hM]
      intro hdvd
      obtain ⟨ρ, _, hρ⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 hdvd
      exact absurd ((Nat.Prime.dvd_factorial hl).1 hρ) (not_le.2 (hlt ρ))

theorem mon_types : MONTypes := by
  classical
  intro C _ _ B _ _ N N' e t ht
  classical
  let p : (Σ b : B, Fin N × Fin (N' b)) → Prop := fun x => x.2.1.val = x.2.2.val
  have hL : Lead p (∑ b : B, dg (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b))) (monAl N (N' b) (e b)))
      (∏ b : B, MvPolynomial.rename (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b)))
        (monP C N (N' b) (e b))) :=
    lead_prod _ _ _ (fun b _ => lead_monP _ (fun r c => Iff.rfl) (e b))
  have hG : Low (∑ b : B, dg (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b))) (monAl N (N' b) (e b)))
      (∏ b : B, monG N (N' b) (e b) fun x => t ⟨b, x⟩) :=
    low_prod _ _ _ (fun b _ => low_monG _ ht (e b))
  rw [jet_eq hL hG, GlobalTheory.LegendreFacts.mfact_eq_prod, Fintype.prod_sigma]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_factorial_diag (e b)]
  apply Finset.prod_congr rfl
  intro y _
  congr 1
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · obtain ⟨r, c⟩ := y
    exact dg_apply _ (fun x y hxy => eq_of_heq (Sigma.mk.inj hxy).2) _ r c
  · intro b' _ hb'
    apply dg_apply_of_notMem
    intro z hz
    exact hb' (congrArg Sigma.fst hz).symm
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem main : MON ∧ MONTypes := by
  exact ⟨mon_one_type, mon_types⟩

end GlobalTheory.MinorGerm
