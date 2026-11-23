import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem ev_h {σ : Type} [Fintype σ] [DecidableEq σ] (x : σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm σ ℂ n) = ∑ s : Sym σ n, ((s : Multiset σ).map x).prod := by
  simp [MvPolynomial.hsymm, map_multiset_prod, Multiset.map_map]

private theorem h_option {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (n + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ n) +
        MvPolynomial.eval (fun i => x (some i)) (MvPolynomial.hsymm σ ℂ (n + 1)) := by
  rw [ev_h, ev_h, ev_h, ← Equiv.sum_comp (symOptionSuccEquiv).symm, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [symOptionSuccEquiv, Equiv.coe_fn_symm_mk, SymOptionSuccEquiv.decode_inl]
    rw [Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [symOptionSuccEquiv, Multiset.map_map, Function.comp_def]

private theorem h_equiv {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (e : σ ≃ τ)
    (x : τ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm τ ℂ n) = MvPolynomial.eval (x ∘ e) (MvPolynomial.hsymm σ ℂ n) := by
  rw [ev_h, ev_h, ← Equiv.sum_comp (Sym.equivCongr e)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Sym.equivCongr, Multiset.map_map]

private theorem h_succ (d : ℕ) (x : Fin (d + 1) → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (n + 1)) =
      x 0 * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ n) +
        MvPolynomial.eval (fun i => x (Fin.succ i)) (MvPolynomial.hsymm (Fin d) ℂ (n + 1)) := by
  rw [h_equiv (finSuccEquiv d).symm x, h_equiv (finSuccEquiv d).symm x, h_option]
  simp

private theorem h_one (x : Fin 1 → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin 1) ℂ n) = x 0 ^ n := by
  rw [ev_h]
  have hs : ∀ s : Sym (Fin 1) n, ((s : Multiset (Fin 1)).map x).prod = x 0 ^ n := by
    intro s
    have hrep : (s : Multiset (Fin 1)).map x = Multiset.replicate n (x 0) := by
      rw [Multiset.eq_replicate]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hb
      rw [Subsingleton.elim a 0]
    rw [hrep, Multiset.prod_replicate]
  rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
  simp

private theorem hq_step (a b : ℂ) (n : ℕ) :
    hq (a + b) (a * b) (n + 1) = a * hq (a + b) (a * b) n + b ^ (n + 1) := by
  induction n with
  | zero => simp [hq.eq_1, hq.eq_2]
  | succ k ih =>
    rw [hq.eq_3, ih]
    ring

theorem UpperTheory.V.Z.Sym.Wt.hqTwo :
    UpperTheory.V.Z.Sym.Wt.HqTwo := by
  intro j a b
  induction j with
  | zero =>
    have h0 : ∀ s : Sym (Fin 2) 0, ((s : Multiset (Fin 2)).map ![a, b]).prod = 1 := by
      intro s
      rw [Subsingleton.elim s Sym.nil]
      simp
    rw [ev_h, Finset.sum_congr rfl fun s _ => h0 s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
    simp [hq.eq_1]
  | succ k ih =>
    rw [hq_step, ← ih]
    refine (h_succ 1 ![a, b] k).trans ?_
    rw [h_one]
    simp
