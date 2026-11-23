import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.CoreBb

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem pderiv_comm' {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial s a =>
    simp only [pderiv_monomial]
    by_cases h : i = j
    · subst h; rfl
    · congr 1
      · rw [tsub_right_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]; ring

theorem prod_map_pow_single {M : Type*} [Monoid M] {ι : Type*} [DecidableEq ι] (P : ι → M)
    (hP : ∀ i j, Commute (P i) (P j)) (e : ι → ℕ) (k : ι) :
    ∀ L : List ι, L.Nodup → k ∈ L →
      (L.map fun i => P i ^ (e i + if i = k then 1 else 0)).prod = (L.map fun i => P i ^ e i).prod * P k
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: L, hL, hk => by
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    have hcomm : ∀ x, Commute (P x) (L.map fun i => P i ^ e i).prod := fun x =>
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hy
        exact (hP x i).pow_right _)
    by_cases hak : a = k
    · subst hak
      have hrest : (L.map fun i => P i ^ (e i + if i = a then 1 else 0)) = L.map fun i => P i ^ e i := by
        apply List.map_congr_left
        intro i hi
        have : i ≠ a := fun h => hL.1 (h ▸ hi)
        simp [this]
      rw [hrest]
      rw [if_pos rfl, pow_succ, mul_assoc, mul_assoc, ← (hcomm a).eq]
    · have hk' : k ∈ L := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm hak
        · exact h
      rw [prod_map_pow_single P hP e k L hL.2 hk']
      simp [hak, mul_assoc]

def Dfun (e : Fin m × Fin n × Bool → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (e k)).prod

theorem pderiv_commute (i j : Fin m × Fin n × Bool) :
    Commute ((pderiv (R := ℂ) i).toLinearMap : Module.End ℂ (PX m n)) (pderiv (R := ℂ) j).toLinearMap :=
  LinearMap.ext fun f => by simp [pderiv_comm' i j f]

theorem Dfun_add_single (e : Fin m × Fin n × Bool → ℕ) (k : Fin m × Fin n × Bool) :
    Dfun (fun i => e i + if i = k then 1 else 0) = Dfun e * ((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) :=
  prod_map_pow_single _ pderiv_commute e k _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))

theorem Dfun_zero : Dfun (m := m) (n := n) (fun _ => 0) = 1 := by
  simp [Dfun]

theorem opMono_eq (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f : PX m n) :
    opMono t f = monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 * Dfun (fun k => t (Sum.inr k)) f := rfl

def opL (s : Sym m n) : Module.End ℂ (PX m n) :=
  ∑ t ∈ s.support, s.coeff t •
    (LinearMap.mulLeft ℂ (monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 : PX m n) ∘ₗ
      Dfun (fun k => t (Sum.inr k)))

theorem op_eq_opL (s : Sym m n) (f : PX m n) : op s f = opL s f := by
  simp [op, opL, opMono_eq, LinearMap.sum_apply]

theorem op_eq_sum_of_subset (s : Sym m n) (f : PX m n) (T : Finset ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ))
    (hT : s.support ⊆ T) : op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset hT fun t _ ht => ?_
  rw [notMem_support_iff.1 ht, zero_smul]

theorem op_add (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq_sum_of_subset (s₁ + s₂) f (s₁.support ∪ s₂.support) support_add,
    op_eq_sum_of_subset s₁ f (s₁.support ∪ s₂.support) Finset.subset_union_left,
    op_eq_sum_of_subset s₂ f (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_add, add_smul]

theorem op_monomial (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (c : ℂ) (f : PX m n) :
    op (monomial t c) f = c • opMono t f := by
  classical
  rw [op_eq_sum_of_subset _ f {t} (support_monomial_subset), Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem op_zero (f : PX m n) : op (0 : Sym m n) f = 0 := by
  simp [op]

theorem op_smul (a : ℂ) (s : Sym m n) (f : PX m n) : op (a • s) f = a • op s f := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c => rw [smul_monomial, op_monomial, op_monomial, smul_eq_mul, mul_smul]
  | add p q hp hq => rw [smul_add, op_add, op_add, hp, hq, smul_add]

theorem op_neg (s : Sym m n) (f : PX m n) : op (-s) f = -op s f := by
  rw [← neg_one_smul ℂ s, op_smul, neg_one_smul]

theorem op_C (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  simp [Dfun_zero]

theorem op_neg_f (s : Sym m n) (f : PX m n) : op s (-f) = -op s f := by
  simp [op_eq_opL]

theorem op_sub_f (s : Sym m n) (f g : PX m n) : op s (f - g) = op s f - op s g := by
  simp [op_eq_opL]

theorem op_zero_f (s : Sym m n) : op s (0 : PX m n) = 0 := by
  simp [op_eq_opL]

theorem op_mul_X_inl (s : Sym m n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    op (s * X (Sum.inl k)) f = X k * op s f := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [X, monomial_mul, mul_one, op_monomial, op_monomial, opMono_eq, opMono_eq]
    have h1 : (t + Finsupp.single (Sum.inl k) 1).comapDomain Sum.inl Sum.inl_injective.injOn =
        t.comapDomain Sum.inl Sum.inl_injective.injOn + Finsupp.single k 1 := by
      ext x; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
    have h2 : (fun x => (t + Finsupp.single (Sum.inl k) 1 : _ →₀ ℕ) (Sum.inr x)) = fun x => t (Sum.inr x) := by
      funext x; simp [Finsupp.single_apply]
    rw [h1, h2, ← mul_one (1 : ℂ), ← monomial_mul, ← X]
    simp only [mul_one, smul_eq_mul]
    ring_nf
    simp [mul_comm, mul_left_comm, mul_assoc, Algebra.mul_smul_comm]
  | add p q hp hq => rw [add_mul, op_add, op_add, hp, hq, mul_add]

theorem op_mul_X_inr (s : Sym m n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    op (s * X (Sum.inr k)) f = op s (pderiv k f) := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [X, monomial_mul, mul_one, op_monomial, op_monomial, opMono_eq, opMono_eq]
    have h1 : (t + Finsupp.single (Sum.inr k) 1).comapDomain Sum.inl Sum.inl_injective.injOn =
        t.comapDomain Sum.inl Sum.inl_injective.injOn := by
      ext x; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
    have h2 : (fun x => (t + Finsupp.single (Sum.inr k) 1 : _ →₀ ℕ) (Sum.inr x)) =
        fun x => t (Sum.inr x) + if x = k then 1 else 0 := by
      funext x; simp [Finsupp.single_apply, eq_comm]
    rw [h1, h2, Dfun_add_single]
    rfl
  | add p q hp hq => rw [add_mul, op_add, op_add, hp, hq]

theorem op_mul_rename_inl (s : Sym m n) (g f : PX m n) :
    op (s * rename Sum.inl g) f = g * op s f := by
  induction g using MvPolynomial.induction_on generalizing s with
  | C a => rw [rename_C, mul_comm, C_mul', op_smul, smul_eq_C_mul]
  | add p q hp hq => rw [map_add, mul_add, op_add, hp, hq, add_mul]
  | mul_X p k hp => rw [map_mul, rename_X, ← mul_assoc, op_mul_X_inl, hp]; ring

theorem KopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) p := by
  simp [KopL, LinearMap.sum_apply]

theorem collapse (P : Fin m → Prop) [DecidablePred P] (c : Fin n) (b : Bool) (F : Fin m → PX m n)
    (k : Fin m × Fin n × Bool) :
    ∑ a ∈ Finset.univ.filter P, (if k = (a, c, b) then F a else 0) =
      if P k.1 ∧ k.2.1 = c ∧ k.2.2 = b then F k.1 else 0 := by
  rw [Finset.sum_filter, Finset.sum_eq_single k.1]
  · obtain ⟨a, c', b'⟩ := k
    by_cases hP : P a <;> by_cases hc : c' = c <;> by_cases hb : b' = b <;> simp [hP, hc, hb]
  · intro a _ ha
    split_ifs with h1 h2
    · exact absurd (by rw [h2]) ha
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem KopL_X (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    KopL ε i j (X k) = if ε k.1 then (if k.2.2 = false ∧ k.2.1 = j then X (k.1, i, false) else 0)
      else (if k.2.2 = true ∧ k.2.1 = i then -X (k.1, j, true) else 0) := by
  classical
  rw [KopL_apply]
  have h1 : ∀ a : Fin m, X (a, i, false) * pderiv (a, j, false) (X k : PX m n) =
      if k = (a, j, false) then X (a, i, false) else 0 := by
    intro a; rw [pderiv_X, Pi.single_apply]; split_ifs <;> simp
  have h2 : ∀ a : Fin m, X (a, j, true) * pderiv (a, i, true) (X k : PX m n) =
      if k = (a, i, true) then X (a, j, true) else 0 := by
    intro a; rw [pderiv_X, Pi.single_apply]; split_ifs <;> simp
  simp only [h1, h2]
  rw [collapse (fun a => ε a = true) j false (fun a => X (a, i, false)) k,
    collapse (fun a => ε a = false) i true (fun a => X (a, j, true)) k]
  obtain ⟨a, c, b⟩ := k
  cases hε : ε a <;> cases b <;> by_cases hcj : c = j <;> by_cases hci : c = i <;> simp [hε, hcj, hci] <;>
    split_ifs <;> simp

theorem KopL_mul (ε : Fin m → Bool) (i j : Fin n) (g h : PX m n) :
    KopL ε i j (g * h) = KopL ε i j g * h + g * KopL ε i j h := by
  rw [KopL_apply, KopL_apply, KopL_apply]
  have e1 : ∀ (p q : Fin m × Fin n × Bool), X p * pderiv q (g * h) = (X p * pderiv q g) * h + g * (X p * pderiv q h) := by
    intro p q; rw [pderiv_mul]; ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem pderiv_KopL (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    pderiv k (KopL ε i j f) = KopL ε i j (pderiv k f) +
      ((if ε k.1 = true ∧ k.2.1 = i ∧ k.2.2 = false then pderiv (k.1, j, false) f else 0) -
        (if ε k.1 = false ∧ k.2.1 = j ∧ k.2.2 = true then pderiv (k.1, i, true) f else 0)) := by
  classical
  rw [KopL_apply, KopL_apply, map_sub, map_sum, map_sum]
  have e1 : ∀ (a : Fin m) (c : Fin n) (b : Bool) (q : Fin m × Fin n × Bool),
      pderiv k (X (a, c, b) * pderiv q f) =
        (if k = (a, c, b) then pderiv q f else 0) + X (a, c, b) * pderiv q (pderiv k f) := by
    intro a c b q
    rw [pderiv_mul, pderiv_X, Pi.single_apply, pderiv_comm' k q f]
    by_cases h : (a, c, b) = k
    · subst h; simp
    · have h' : ¬ k = (a, c, b) := fun e => h e.symm
      simp [h, h']
  simp only [e1, Finset.sum_add_distrib]
  rw [collapse (fun a => ε a = true) i false (fun a => pderiv (a, j, false) f) k,
    collapse (fun a => ε a = false) j true (fun a => pderiv (a, i, true) f) k]
  ring

theorem KopL_pderiv (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    KopL ε i j (pderiv k f) - pderiv k (KopL ε i j f) =
      if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -pderiv (k.1, j, false) f else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then pderiv (k.1, i, true) f else 0) := by
  rw [pderiv_KopL]
  obtain ⟨a, c, b⟩ := k
  cases hε : ε a <;> cases b <;> by_cases hcj : c = j <;> by_cases hci : c = i <;> simp [hε, hcj, hci] <;>
    split_ifs <;> simp

theorem symK_inl (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    symK ε i j (X (Sum.inl k)) = rename Sum.inl (KopL ε i j (X k)) := by
  rw [symK, mkDerivation_X, Sum.elim_inl, KopL_X]
  split_ifs <;> simp

theorem symK_inr (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    symK ε i j (X (Sum.inr k)) = if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -X (Sum.inr (k.1, j, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then X (Sum.inr (k.1, i, true)) else 0) := by
  rw [symK, mkDerivation_X, Sum.elim_inr]

theorem symK_op (ε : Fin m → Bool) (i j : Fin n) (s : Sym m n) :
    ∀ f : PX m n, op (symK ε i j s) f = KopL ε i j (op s f) - op s (KopL ε i j f) := by
  induction s using MvPolynomial.induction_on with
  | C a =>
    intro f
    rw [MvPolynomial.derivation_C, op_zero, op_C, op_C, map_smul, sub_self]
  | add p q hp hq =>
    intro f
    rw [map_add, op_add, hp, hq, op_add, op_add, map_add]
    abel
  | mul_X p k hp =>
    intro f
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, op_add, mul_comm (X k) (symK ε i j p)]
    cases k with
    | inl k =>
      rw [symK_inl, op_mul_rename_inl, op_mul_X_inl, hp, op_mul_X_inl, op_mul_X_inl, KopL_mul]
      ring
    | inr k =>
      rw [op_mul_X_inr, hp, op_mul_X_inr, op_mul_X_inr]
      have key : op (p * symK ε i j (X (Sum.inr k))) f =
          op p (KopL ε i j (pderiv k f)) - op p (pderiv k (KopL ε i j f)) := by
        rw [← op_sub_f, KopL_pderiv, symK_inr]
        split_ifs <;> simp [mul_neg, op_neg, op_mul_X_inr, op_neg_f, op_zero_f, op_zero]
      rw [key]
      abel

theorem _root_.PositivityTheory.Rg.Sw.LC.symKComm : SymKComm := fun _ _ ε i j s _ f _ => symK_op ε i j s f

end PositivityTheory.Rg.Sw.LC.CoreBb
