import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.B1

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

local notation "σ" => Fin m × Fin n × Bool

theorem pderiv_pow_monomial (i : σ) (e : ℕ) (s : σ →₀ ℕ) (a : ℂ) :
    (((pderiv (R := ℂ) i).toLinearMap ^ e) (monomial s a) : PX m n) =
      monomial (s - Finsupp.single i e) (a * ((s i).descFactorial e : ℂ)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    show (pderiv (R := ℂ) i) (monomial _ _) = _
    rw [pderiv_monomial]
    have e1 : s - Finsupp.single i e - Finsupp.single i 1 = s - Finsupp.single i (e + 1) := by
      ext k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have h : (s - Finsupp.single i e) i = s i - e := by simp
    rw [e1, h, Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

theorem list_single_apply (γ : σ → ℕ) (l : List σ) (k : σ) (hk : k ∉ l) :
    (l.map fun k => Finsupp.single k (γ k)).sum k = 0 := by
  induction l with
  | nil => simp
  | cons k' l' ih =>
    rw [List.mem_cons, not_or] at hk
    simp only [List.map_cons, List.sum_cons, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
      if_neg (Ne.symm hk.1), zero_add]
    exact ih hk.2

theorem list_pderiv (γ : σ → ℕ) (l : List σ) (hl : l.Nodup) (s : σ →₀ ℕ) (a : ℂ) :
    ((l.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (γ k)).prod (monomial s a) : PX m n) =
      monomial (s - (l.map fun k => Finsupp.single k (γ k)).sum)
        (a * (l.map fun k => ((s k).descFactorial (γ k) : ℂ)).prod) := by
  induction l generalizing s a with
  | nil => simp
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Module.End.mul_apply]
    rw [ih hl.2, pderiv_pow_monomial]
    have hk := list_single_apply γ l k hl.1
    have e1 : s - (l.map fun k => Finsupp.single k (γ k)).sum - Finsupp.single k (γ k) =
        s - (Finsupp.single k (γ k) + (l.map fun k => Finsupp.single k (γ k)).sum) := by
      ext k'
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; rw [hk]; omega
      · omega
    have e2 : (s - (l.map fun k => Finsupp.single k (γ k)).sum) k = s k := by
      simp [hk]
    rw [e1, e2]
    congr 1
    ring

theorem opMono_add (t : σ ⊕ σ →₀ ℕ) (f g : PX m n) : opMono t (f + g) = opMono t f + opMono t g := by
  unfold opMono; rw [map_add, mul_add]

theorem opMono_smul (t : σ ⊕ σ →₀ ℕ) (c : ℂ) (f : PX m n) : opMono t (c • f) = c • opMono t f := by
  unfold opMono; rw [map_smul, mul_smul_comm]

theorem opMono_zero (t : σ ⊕ σ →₀ ℕ) : opMono t (0 : PX m n) = 0 := by
  unfold opMono; rw [map_zero, mul_zero]

theorem op_eq_sum (s : Sym m n) (S : Finset (σ ⊕ σ →₀ ℕ)) (h : s.support ⊆ S) (f : PX m n) :
    op s f = ∑ t ∈ S, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset h fun t _ ht => ?_
  rw [MvPolynomial.notMem_support_iff.mp ht, zero_smul]

theorem op_add (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq_sum (s₁ + s₂) _ MvPolynomial.support_add, op_eq_sum s₁ (s₁.support ∪ s₂.support) Finset.subset_union_left,
    op_eq_sum s₂ (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [coeff_add, add_smul]

theorem op_smul (c : ℂ) (s : Sym m n) (f : PX m n) : op (c • s) f = c • op s f := by
  rw [op_eq_sum (c • s) s.support MvPolynomial.support_smul, op]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_smul]

theorem op_zero (f : PX m n) : op (0 : Sym m n) f = 0 := by
  simp [op]

theorem op_sum {ι : Type*} (S : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ S, g i) f = ∑ i ∈ S, op (g i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]

theorem op_monomial (t : σ ⊕ σ →₀ ℕ) (c : ℂ) (f : PX m n) : op (monomial t c) f = c • opMono t f := by
  classical
  rw [op_eq_sum (monomial t c) {t} (support_monomial_subset), Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem op_f_add (s : Sym m n) (f g : PX m n) : op s (f + g) = op s f + op s g := by
  unfold op; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [opMono_add, smul_add]

theorem op_f_smul (s : Sym m n) (c : ℂ) (f : PX m n) : op s (c • f) = c • op s f := by
  unfold op; rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [opMono_smul, smul_comm]

theorem op_f_zero (s : Sym m n) : op s (0 : PX m n) = 0 := by
  unfold op; exact Finset.sum_eq_zero fun t _ => by rw [opMono_zero, smul_zero]

theorem comap_inl_add (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) :
    (t + Finsupp.mapDomain Sum.inl μ).comapDomain Sum.inl Sum.inl_injective.injOn =
      t.comapDomain Sum.inl Sum.inl_injective.injOn + μ := by
  ext k
  simp [Finsupp.comapDomain_apply, Finsupp.mapDomain_apply Sum.inl_injective]

theorem inr_add (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (k : σ) :
    ((t + Finsupp.mapDomain Sum.inl μ : σ ⊕ σ →₀ ℕ)) (Sum.inr k) = t (Sum.inr k) := by
  rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, add_zero]
  rintro ⟨x, hx⟩; exact Sum.inl_ne_inr hx

theorem opMono_shiftL (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (f : PX m n) :
    opMono (t + Finsupp.mapDomain Sum.inl μ) f = monomial μ 1 * opMono t f := by
  unfold opMono
  rw [comap_inl_add]
  simp only [inr_add]
  rw [← mul_assoc, monomial_mul, one_mul, add_comm]

theorem op_mulL (μ : σ →₀ ℕ) (s : Sym m n) (f : PX m n) :
    op (monomial (Finsupp.mapDomain Sum.inl μ) 1 * s) f = monomial μ 1 * op s f := by
  conv_lhs => rw [s.as_sum, Finset.mul_sum]
  rw [op_sum]
  conv_rhs => rw [op, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, one_mul, op_monomial, add_comm, opMono_shiftL, mul_smul_comm]

theorem op_renameL (p : PX m n) (s : Sym m n) (f : PX m n) : op (rename Sum.inl p * s) f = p * op s f := by
  conv_lhs => rw [p.as_sum, map_sum, Finset.sum_mul]
  conv_rhs => rw [p.as_sum, Finset.sum_mul]
  rw [op_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : (monomial (Finsupp.mapDomain Sum.inl μ) (coeff μ p) : Sym m n) =
      coeff μ p • monomial (Finsupp.mapDomain Sum.inl μ) 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : (monomial μ (coeff μ p) : PX m n) = coeff μ p • monomial μ 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [rename_monomial, h1, h2, smul_mul_assoc, op_smul, op_mulL, smul_mul_assoc]

theorem opMono_inr (γ δ : σ →₀ ℕ) :
    opMono (Finsupp.mapDomain Sum.inr γ) (monomial δ 1 : PX m n) =
      monomial (δ - γ) (∏ k, ((δ k).descFactorial (γ k) : ℂ)) := by
  unfold opMono
  have h0 : ((Finsupp.mapDomain Sum.inr γ : σ ⊕ σ →₀ ℕ)).comapDomain Sum.inl
      (Sum.inl_injective (α := σ) (β := σ)).injOn = (0 : σ →₀ ℕ) := by
    ext k
    rw [Finsupp.comapDomain_apply, Finsupp.mapDomain_of_notMem_range]
    · rfl
    · rintro ⟨x, hx⟩; exact Sum.inr_ne_inl hx
  rw [h0]
  simp only [Finsupp.mapDomain_apply Sum.inr_injective]
  rw [list_pderiv γ _ (Finset.nodup_toList _), Finset.prod_map_toList, Finset.sum_map_toList,
    Finsupp.univ_sum_single]
  rw [← C_apply, C_1, one_mul, one_mul]

variable (ε : Fin m → Bool)

def GoodT (t : σ ⊕ σ →₀ ℕ) : Prop := ∀ k, (t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0) → inF1 ε k

theorem sf_monomial (t : σ ⊕ σ →₀ ℕ) (c : ℂ) (ht : GoodT ε t) : SymbolInFirstFamily ε (monomial t c : Sym m n) := by
  classical
  intro u hu
  have := support_monomial_subset hu
  rw [Finset.mem_singleton] at this
  subst this; exact ht

theorem sf_zero : SymbolInFirstFamily ε (0 : Sym m n) := by intro t ht; simp at ht

theorem sf_add {s₁ s₂ : Sym m n} (h₁ : SymbolInFirstFamily ε s₁) (h₂ : SymbolInFirstFamily ε s₂) : SymbolInFirstFamily ε (s₁ + s₂) := by
  classical
  intro t ht
  rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
  · exact h₁ t h
  · exact h₂ t h

theorem sf_smul {s : Sym m n} (c : ℂ) (h : SymbolInFirstFamily ε s) : SymbolInFirstFamily ε (c • s) := fun t ht => h t (MvPolynomial.support_smul ht)

theorem sf_sub {s₁ s₂ : Sym m n} (h₁ : SymbolInFirstFamily ε s₁) (h₂ : SymbolInFirstFamily ε s₂) : SymbolInFirstFamily ε (s₁ - s₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ s₂]; exact sf_add ε h₁ (sf_smul ε _ h₂)

theorem sf_sum {ι : Type*} (S : Finset ι) (g : ι → Sym m n) (h : ∀ i ∈ S, SymbolInFirstFamily ε (g i)) : SymbolInFirstFamily ε (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using sf_zero ε
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact sf_add ε (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem goodT_add_inl (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (ht : GoodT ε t) (hμ : ∀ k ∈ μ.support, inF1 ε k) :
    GoodT ε (Finsupp.mapDomain Sum.inl μ + t) := by
  intro k hk
  simp only [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective] at hk
  have h2 : (Finsupp.mapDomain Sum.inl μ : σ ⊕ σ →₀ ℕ) (Sum.inr k) = 0 := by
    rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨x, hx⟩; exact Sum.inl_ne_inr hx
  rw [h2, zero_add] at hk
  by_cases hμk : μ k = 0
  · rw [hμk, zero_add] at hk; exact ht k hk
  · exact hμ k (Finsupp.mem_support_iff.mpr hμk)

theorem sf_mulL (μ : σ →₀ ℕ) (hμ : ∀ k ∈ μ.support, inF1 ε k) {s : Sym m n} (h : SymbolInFirstFamily ε s) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inl μ) c * s) := by
  rw [s.as_sum, Finset.mul_sum]
  refine sf_sum ε _ _ fun t ht => ?_
  rw [monomial_mul]
  exact sf_monomial ε _ _ (goodT_add_inl ε t μ (h t ht) hμ)

theorem sf_renameL (p : PX m n) (hp : p ∈ F1 ε) {s : Sym m n} (h : SymbolInFirstFamily ε s) : SymbolInFirstFamily ε (rename Sum.inl p * s) := by
  rw [p.as_sum, map_sum, Finset.sum_mul]
  refine sf_sum ε _ _ fun μ hμ => ?_
  rw [rename_monomial]
  refine sf_mulL ε μ (fun k hk => ?_) h _
  have hv : k ∈ p.vars := (MvPolynomial.mem_vars k).mpr ⟨μ, hμ, hk⟩
  exact (MvPolynomial.mem_supported.mp hp) hv

theorem sf_inr (γ : σ →₀ ℕ) (hγ : ∀ k ∈ γ.support, inF1 ε k) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inr γ) c : Sym m n) := by
  refine sf_monomial ε _ _ fun k hk => ?_
  have h1 : (Finsupp.mapDomain Sum.inr γ : σ ⊕ σ →₀ ℕ) (Sum.inl k) = 0 := by
    rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨x, hx⟩; exact Sum.inr_ne_inl hx
  rw [h1, Finsupp.mapDomain_apply Sum.inr_injective] at hk
  exact hγ k (Finsupp.mem_support_iff.mpr (hk.resolve_left (by simp)))

theorem indicator (Γ : Finset (σ →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k) :
    ∀ N, ∀ γ ∈ Γ, (Γ.filter (γ < ·)).card ≤ N →
      ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ ∈ Γ, op P (monomial δ 1) = if δ = γ then 1 else 0 := by
  classical
  intro N
  induction N with
  | zero =>
    intro γ hγ hc
    exact aux Γ hΓ γ hγ (fun δ hδ => by
      exfalso
      have : 0 < (Γ.filter (γ < ·)).card := Finset.card_pos.mpr ⟨δ, hδ⟩
      omega)
  | succ N ih =>
    intro γ hγ hc
    refine aux Γ hΓ γ hγ fun δ hδ => ih δ (Finset.mem_filter.mp hδ).1 ?_
    have hlt : (Γ.filter (δ < ·)).card < (Γ.filter (γ < ·)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_trans (Finset.mem_filter.mp hδ).2 hx.2⟩
      · have := hsub hδ
        rw [Finset.mem_filter] at this
        exact lt_irrefl _ this.2
    omega
where
  aux (Γ : Finset (σ →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k) (γ : σ →₀ ℕ) (hγ : γ ∈ Γ)
      (hex : ∀ δ ∈ Γ.filter (γ < ·), ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ' ∈ Γ, op P (monomial δ' 1) = if δ' = δ then 1 else 0) :
      ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ ∈ Γ, op P (monomial δ 1) = if δ = γ then 1 else 0 := by
    classical
    choose! Q hQ using hex
    let g : ℂ := ∏ k, (((γ k).factorial : ℕ) : ℂ)
    let D : (σ →₀ ℕ) → ℂ := fun δ => g⁻¹ * ∏ k, ((δ k).descFactorial (γ k) : ℂ)
    refine ⟨(g⁻¹ : ℂ) • monomial (Finsupp.mapDomain Sum.inr γ) 1 -
      ∑ δ ∈ Γ.filter (γ < ·), D δ • (monomial (Finsupp.mapDomain Sum.inl (δ - γ)) 1 * Q δ), ?_, ?_⟩
    · refine sf_sub ε (sf_smul ε _ (sf_inr ε γ (hΓ γ hγ) 1)) (sf_sum ε _ _ fun δ hδ => sf_smul ε _ ?_)
      refine sf_mulL ε _ (fun k hk => ?_) (hQ δ hδ).1 1
      have : (δ - γ) k ≠ 0 := Finsupp.mem_support_iff.mp hk
      exact hΓ δ (Finset.mem_filter.mp hδ).1 k (Finsupp.mem_support_iff.mpr (by
        rw [Finsupp.tsub_apply] at this; omega))
    · intro δ' hδ'
      rw [sub_eq_add_neg, op_add, ← neg_one_smul ℂ (∑ δ ∈ _, _), op_smul, op_smul, op_sum, op_monomial, opMono_inr]
      have hsum : ∑ δ ∈ Γ.filter (γ < ·), op (D δ • (monomial (Finsupp.mapDomain Sum.inl (δ - γ)) 1 * Q δ))
          (monomial δ' 1 : PX m n) = if γ < δ' then D δ' • (monomial (δ' - γ) 1 : PX m n) else 0 := by
        rw [Finset.sum_congr rfl fun δ hδ => by rw [op_smul, op_mulL, (hQ δ hδ).2 δ' hδ']]
        simp only [mul_ite, mul_one, mul_zero, smul_ite, smul_zero]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_filter, hδ', true_and]
      rw [hsum]
      have hmain : (g⁻¹ : ℂ) • (1 : ℂ) • (monomial (δ' - γ) (∏ k, ((δ' k).descFactorial (γ k) : ℂ)) : PX m n) =
          D δ' • monomial (δ' - γ) 1 := by
        rw [one_smul, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_one]
      rw [hmain]
      by_cases hlt : γ < δ'
      · rw [if_pos hlt, if_neg (ne_of_gt hlt)]; simp
      · rw [if_neg hlt]
        by_cases he : δ' = γ
        · subst he
          rw [if_pos rfl]
          have hD : D δ' = 1 := by
            simp only [D, g, Nat.descFactorial_self]
            rw [inv_mul_cancel₀]
            exact Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast Nat.factorial_ne_zero _
          rw [hD, one_smul, tsub_self, ← C_apply, C_1]; simp
        · rw [if_neg he]
          have hnle : ¬ γ ≤ δ' := fun hle => hlt (lt_of_le_of_ne hle (Ne.symm he))
          obtain ⟨k, hk⟩ : ∃ k, δ' k < γ k := by
            by_contra hcon
            push_neg at hcon
            exact hnle (fun k => hcon k)
          have hD : D δ' = 0 := by
            simp only [D]
            rw [Finset.prod_eq_zero (Finset.mem_univ k) (by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hk),
              mul_zero]
          rw [hD, zero_smul]; simp

end PositivityTheory.Rg.Sw.LC.B1

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.B1

theorem dens : Dens := by
  intro m n ε R T hT
  classical
  let M : ℕ := R.sup (fun r => Finset.univ.sup r)
  let bnd : (Fin m × Fin n × Bool) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => M)
  let Γ := (Finset.Iic bnd).filter (fun δ => (∀ k ∈ δ.support, inF1 ε k) ∧ rdeg ε δ ∈ R)
  have hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k := fun γ hγ => (Finset.mem_filter.mp hγ).2.1
  have memΓ : ∀ δ : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k ∈ δ.support, inF1 ε k) → rdeg ε δ ∈ R → δ ∈ Γ := by
    intro δ h1 h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr fun k => ?_, h1, h2⟩
    show δ k ≤ M
    by_cases hk : δ k = 0
    · omega
    · have hF := h1 k (Finsupp.mem_support_iff.mpr hk)
      have hkeq : k = (k.1, k.2.1, !ε k.1) := by
        obtain ⟨a, i, b⟩ := k; simp only [inF1] at hF; simp [hF]
      have h3 : δ k ≤ rdeg ε δ k.1 := by
        unfold rdeg
        conv_lhs => rw [hkeq]
        exact Finset.single_le_sum (f := fun i => δ (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k.2.1)
      have h4 : rdeg ε δ k.1 ≤ Finset.univ.sup (rdeg ε δ) := Finset.le_sup (f := rdeg ε δ) (Finset.mem_univ _)
      have h5 : Finset.univ.sup (rdeg ε δ) ≤ M := Finset.le_sup (f := fun r => Finset.univ.sup r) h2
      omega
  have mono_mem : ∀ γ ∈ Γ, (monomial γ 1 : PX m n) ∈ box ε (R : Set (Fin m → ℕ)) := fun γ hγ =>
    Submodule.subset_span ⟨γ, hΓ γ hγ, (Finset.mem_filter.mp hγ).2.2, rfl⟩
  have hind := indicator ε Γ hΓ Γ.card
  choose! P hP using fun γ (hγ : γ ∈ Γ) => hind γ hγ (Finset.card_filter_le _ _)
  refine ⟨∑ γ ∈ Γ, rename Sum.inl (T (monomial γ 1)) * P γ,
    sf_sum ε _ _ fun γ hγ => sf_renameL ε _ (hT _ (mono_mem γ hγ)) (hP γ hγ).1, ?_⟩
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, h1, h2, rfl⟩ := hx
    have hδ := memΓ δ h1 h2
    rw [op_sum]
    simp only [op_renameL]
    rw [Finset.sum_congr rfl fun γ hγ => by rw [(hP γ hγ).2 δ hδ]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hδ]
  | zero => rw [op_f_zero, map_zero]
  | add x y _ _ hx hy => rw [op_f_add, map_add, hx, hy]
  | smul a x _ hx => rw [op_f_smul, map_smul, hx]

end PositivityTheory.Rg.Sw.LC
