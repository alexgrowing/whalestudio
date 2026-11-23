import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwUnitHk
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSatakeIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

private theorem anti_of_gap {n : ℕ} {c : Fin n → ℤ} {N : ℕ} (h : ∀ i j, i < j → c j + N ≤ c i) : Antitone c := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have := h i j hlt
    omega

private theorem gap_add {n : ℕ} {c : Fin n → ℤ} (a : Fin n →₀ ℕ) {N : ℕ}
    (h : ∀ i j, i < j → c j + ((a.degree + N : ℕ) : ℤ) ≤ c i) :
    ∀ i j, i < j → (c + fun i => (a i : ℤ)) j + N ≤ (c + fun i => (a i : ℤ)) i := by
  intro i j hij
  have h1 := h i j hij
  have h2 : a j ≤ a.degree := Finsupp.le_degree j a
  simp only [Pi.add_apply]
  push_cast at h1
  omega

private theorem anti_fund (n m : ℕ) : Antitone (fund n m) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [fund]
  split_ifs <;> omega

private theorem abs_mono {n : ℕ} {A H : Type} [CommRing A] [Ring H] [Algebra A H] (q : A)
    (T : (Fin n → ℤ) → H) (th : MvPolynomial (Fin n) A →ₐ[A] H)
    (hmul : ∀ c d, Antitone c → Antitone d → T c * T d = T (c + d))
    (hu : ∀ c, Antitone c → IsUnit (T c))
    (hX : ∀ i : Fin n, th (MvPolynomial.X i) * T (fund n i) = (q ^ (i : ℕ)) • T (fund n ((i : ℕ) + 1)))
    (a : Fin n →₀ ℕ) : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (a.degree : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial a 1) = q ^ m • T (c + fun i => (a i : ℤ)) := by
  have hadd : ∀ a b : Fin n →₀ ℕ,
      (∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (a.degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial a 1) = q ^ m • T (c + fun i => (a i : ℤ))) →
      (∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (b.degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial b 1) = q ^ m • T (c + fun i => (b i : ℤ))) →
      ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + ((a + b).degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial (a + b) 1) = q ^ m • T (c + fun i => ((a + b) i : ℤ)) := by
    intro a b ha hb c hc
    rw [map_add] at hc
    obtain ⟨m, hm⟩ := ha c fun i j hij => by
      have := hc i j hij
      push_cast at this
      omega
    obtain ⟨m', hm'⟩ := hb _ (gap_add a hc)
    refine ⟨m + m', ?_⟩
    have e : (MvPolynomial.monomial (a + b) (1 : A)) = MvPolynomial.monomial a 1 * MvPolynomial.monomial b 1 := by
      rw [MvPolynomial.monomial_mul, one_mul]
    rw [e, map_mul, ← mul_assoc, hm, smul_mul_assoc, hm', smul_smul, pow_add]
    congr 2
    ext i
    simp [add_assoc]
  have h0 : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + ((0 : Fin n →₀ ℕ).degree : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial 0 1) = q ^ m • T (c + fun i => ((0 : Fin n →₀ ℕ) i : ℤ)) := by
    intro c _
    refine ⟨0, ?_⟩
    have : (c + fun i => ((0 : Fin n →₀ ℕ) i : ℤ)) = c := by ext i; simp
    rw [this]
    simp
  have h1 : ∀ l : Fin n, ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (((Finsupp.single l 1 : Fin n →₀ ℕ).degree : ℕ) : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial (Finsupp.single l 1) 1) =
        q ^ m • T (c + fun i => ((Finsupp.single l 1 : Fin n →₀ ℕ) i : ℤ)) := by
    intro l c hc
    refine ⟨l, ?_⟩
    have hc' : Antitone (c + fun i => ((Finsupp.single l 1 : Fin n →₀ ℕ) i : ℤ)) :=
      anti_of_gap (N := 0) (gap_add _ (by simpa using hc))
    apply (hu _ (anti_fund n l)).mul_right_cancel
    change T c * th (MvPolynomial.X l) * _ = _
    rw [mul_assoc, hX, mul_smul_comm, smul_mul_assoc, hmul _ _ (anti_of_gap hc) (anti_fund _ _),
      hmul _ _ hc' (anti_fund _ _)]
    congr 2
    ext i
    simp only [Pi.add_apply, fund, Finsupp.single_apply, Fin.ext_iff]
    split_ifs <;> push_cast <;> omega
  induction a using Finsupp.induction_linear with
  | zero => exact h0
  | add a b ha hb => exact hadd a b ha hb
  | single l m =>
    induction m with
    | zero => rw [Finsupp.single_zero]; exact h0
    | succ m ih => rw [Finsupp.single_add]; exact hadd _ _ ih (h1 l)

private theorem abs_faith {n : ℕ} {A H : Type} [CommRing A] [Ring H] [Algebra A H] (q : A) (hq : IsUnit q)
    (T : (Fin n → ℤ) → H) (th : MvPolynomial (Fin n) A →ₐ[A] H) (e : H)
    (hmul : ∀ c d, Antitone c → Antitone d → T c * T d = T (c + d))
    (hu : ∀ c, Antitone c → IsUnit (T c))
    (hX : ∀ i : Fin n, th (MvPolynomial.X i) * T (fund n i) = (q ^ (i : ℕ)) • T (fund n ((i : ℕ) + 1)))
    (hli : LinearIndependent A fun a : {a : Fin n → ℤ // Antitone a} => T a.1 * e)
    (p : MvPolynomial (Fin n) A) (hp : th p * e = 0) : p = 0 := by
  classical
  set N : ℕ := p.support.sup Finsupp.degree with hN
  let c : Fin n → ℤ := fun i => -((i : ℕ) : ℤ) * N
  have hc : ∀ a : p.support, ∀ i j, i < j → c j + (a.1.degree : ℤ) ≤ c i := by
    intro a i j hij
    have h1 : a.1.degree ≤ N := Finset.le_sup (f := Finsupp.degree) a.2
    have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
    have h3 : (a.1.degree : ℤ) ≤ N := by exact_mod_cast h1
    have h4 : (0 : ℤ) ≤ N := Int.natCast_nonneg _
    simp only [c]
    nlinarith
  choose m hm using fun a : p.support => abs_mono q T th hmul hu hX a.1 c (hc a)
  let f : p.support → {a : Fin n → ℤ // Antitone a} := fun a =>
    ⟨c + fun i => (a.1 i : ℤ), anti_of_gap (N := 0) (gap_add _ (by simpa using hc a))⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, add_right_inj] at this
    ext i
    exact_mod_cast congrFun this i
  have hli' := Fintype.linearIndependent_iff.1 (hli.comp f hf) (fun a => p.coeff a.1 * q ^ m a) (by
    have h0 : T c * (th p * e) = 0 := by rw [hp, mul_zero]
    rw [← h0]
    conv_rhs => rw [p.as_sum, ← Finset.sum_coe_sort, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : MvPolynomial.monomial a.1 (p.coeff a.1) = p.coeff a.1 • MvPolynomial.monomial a.1 (1 : A) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hm, smul_mul_assoc, smul_smul]
    rfl)
  ext a
  by_contra ha
  have ha' : a ∈ p.support := by simpa using ha
  have := hli' ⟨a, ha'⟩
  exact ha (by simpa using ((hq.pow _).mul_left_eq_zero).1 this)

private theorem dom_pw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {x : kˣ} (hx : IsUnif x) {c : Fin n → ℤ} (hc : Antitone c) : Dom fun i => x ^ c i := by
  obtain ⟨p, -, hp⟩ := hx
  intro i j hij
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  have h0 : 0 < valuation k (x : k) := by simp [zero_lt_iff]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hc hij)

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.bernFaith :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤)), (∀ w, b.T w = hT A (iwC k n ⊤) (pm k n w)) → (∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) → b.Faithful := by
  intro k _ _ _ _ n A _ x hx hq b hT' hX p hp
  refine abs_faith (resCard k : A) hq (fun c => hT A (iwC k n ⊤) (pw x c)) b.th b.one ?_ ?_ hX ?_ p hp
  · intro c d hc hd
    apply Subtype.ext
    have := (domMul k n ⊤ A _ (permRep A (iwC k n ⊤))).1 _ _ (dom_pw hx hc) (dom_pw hx hd)
    refine this.trans ?_
    have e : ((fun i => x ^ c i) * fun i => x ^ d i) = fun i => x ^ (c + d) i := by
      ext1 i
      simp [_root_.zpow_add]
    rw [e]
    rfl
  · intro c hc
    exact (unitHk k n A hq).2 _ (dom_pw hx hc)
  · have := satakeIndep k n A x hx
    simpa only [Hk.Bern.one, hT'] using this
