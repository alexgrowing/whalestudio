import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulAddCharLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEvaluateEntryOfMulLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionLowerEntryMultiplicationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionUpperFreeEntryTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiRowAddStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem fillAt_entry (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]

theorem red_mul_entry (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E) (g : k → ℂ) (Φ : Matrix R Q k → ℂ)
    (x : Matrix R Q k) :
    red ψ ν w β E I (fun t => g (t e.1 e.2) * Φ t) x = g (x e.1 e.2) * red ψ ν w β E I Φ x := by
  unfold red
  simp_rw [fillAt_entry β E I x _ e hI hE, mul_assoc]
  exact integral_const_mul _ _

theorem fillAt_add_single (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I x y + Matrix.single e.1 e.2 a = fillAt β E I (x + Matrix.single e.1 e.2 a) y := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]

theorem circle_neg_mul (ψ : AddChar k Circle) (z : k) : (ψ (-z) : ℂ) * (ψ z : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem evalLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (b : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) →
      L Φ' = L Φ) :
    EvalLaw L ψ ν w β E I e := by
  intro b Φ
  let f : Matrix R Q k →ₗ[k] k :=
    { toFun := fun t => b * t e.1 e.2
      map_add' := fun s t => by simp [mul_add]
      map_smul' := fun a t => by simp; ring }
  have hmem : (fun t => (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm k ψ hψ R Q f (-(b * β e.1 e.2)) Φ.1 Φ.2
    convert this using 3 with t
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    ring_nf
  refine ⟨⟨_, hmem⟩, h b Φ ⟨_, hmem⟩ (fun t => rfl), fun x => ?_⟩
  exact red_mul_entry ψ ν w β E I e hI hE (fun s => (ψ (b * (s - β e.1 e.2)) : ℂ)) Φ.1 x

theorem intLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (a : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single e.1 e.2 a)) →
      L Φ' = (ψ (w (Matrix.single e.1 e.2 a)) : ℂ) • L Φ) :
    IntLaw L ψ ν w β E I e := by
  intro a Φ
  have hmem1 : (fun t => Φ.1 (t + Matrix.single e.1 e.2 a)) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k R Q 1 (Matrix.single e.1 e.2 a) Φ.1 Φ.2
    simpa using this
  let Φa : SB (Matrix R Q k) := ⟨_, hmem1⟩
  refine ⟨(ψ (-w (Matrix.single e.1 e.2 a)) : ℂ) • Φa, ?_, fun x => ?_⟩
  · rw [map_smul, h a Φ Φa (fun t => rfl), smul_smul, circle_neg_mul, one_smul]
  · unfold red
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Φa]
    congr 1
    funext y
    rw [← fillAt_add_single β E I x y e hI hE a, map_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring

theorem kills_empty (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) : Kills L ψ ν w β ∅ ∅ := by
  intro Φ hΦ
  have h0 : Φ = 0 := by
    apply Subtype.ext
    funext x
    have hx := congrFun hΦ x
    unfold red at hx
    have hf : ∀ y : (∅ : Finset (R × Q)) → k, fillAt β ∅ ∅ x y = x := fun y => by ext r q; simp [fillAt]
    simp only [hf] at hx
    rw [integral_const] at hx
    have hv : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν) Set.univ = 1 := by
      rw [Measure.pi_of_empty]; simp
    have hv' : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν).real Set.univ = 1 := by
      simp [Measure.real, hv]
    rw [hv', one_smul, Pi.zero_apply] at hx
    rw [Submodule.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hx).resolve_right (Circle.coe_ne_zero _)
  rw [h0, map_zero]

end Glue
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem kills_evals (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (I : Finset (R × Q)) (S : Finset (R × Q)) : ∀ E : Finset (R × Q), Disjoint S I → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ E' : Finset (R × Q), E ⊆ E' → E' ⊆ E ∪ S → e ∉ E' → EvalLaw L ψ ν w β E' I e) →
    Kills L ψ ν w β (E ∪ S) I := by
  induction S using Finset.induction_on with
  | empty => intro E _ hK _; simpa using hK
  | insert a S ha ih =>
    intro E hdisj hK hlaw
    have hdisj' : Disjoint S I := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β (E ∪ S) I := ih E hdisj' hK fun e he E' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) E' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haI : a ∉ I := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : E ∪ insert a S = insert a (E ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haE : a ∈ E ∪ S
    · rwa [Finset.insert_eq_of_mem haE]
    · refine GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law k ψ ν hψ hψ1 hν R Q M L w β (E ∪ S) I a haI h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (E ∪ S) Finset.subset_union_left ?_ haE
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

theorem kills_ints (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E : Finset (R × Q)) (S : Finset (R × Q)) : ∀ I : Finset (R × Q), Disjoint S E → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ I' : Finset (R × Q), I ⊆ I' → I' ⊆ I ∪ S → e ∉ I' → IntLaw L ψ ν w β E I' e) →
    Kills L ψ ν w β E (I ∪ S) := by
  induction S using Finset.induction_on with
  | empty => intro I _ hK _; simpa using hK
  | insert a S ha ih =>
    intro I hdisj hK hlaw
    have hdisj' : Disjoint S E := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β E (I ∪ S) := ih I hdisj' hK fun e he I' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) I' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haE : a ∉ E := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : I ∪ insert a S = insert a (I ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haI : a ∈ I ∪ S
    · rwa [Finset.insert_eq_of_mem haI]
    · refine GlobalTheory.T.partialReduction_integrate_entry_of_translation k ψ ν hψ hν R Q M L w β E (I ∪ S) a haE h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (I ∪ S) Finset.subset_union_left ?_ haI
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

end Glue2
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Sets
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_fixSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ fixSet ρ ↔
    ((∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨ (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)) := by
  simp [fixSet]

theorem mem_transSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ transSet ρ ↔
    (Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val) := by
  simp [transSet]

theorem mem_lowSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ lowSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by
  simp [lowSet]

theorem mem_upSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ upSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ := by
  simp [upSet]

theorem disj_trans_fix (ρ : ℕ) :
    Disjoint (transSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ) := by
  rw [Finset.disjoint_left]
  rintro ⟨r, q⟩ h1 h2
  rw [mem_transSet] at h1
  rw [mem_fixSet] at h2
  rcases h2 with ⟨i, hq, hi, hnf⟩ | ⟨l, s, hr, hl, hq⟩
  · exact hnf h1.1
  · dsimp only at hr hq
    subst hr hq
    have := h1.1
    simp only [Free] at this
    omega

theorem disj_low_trans (ρ : ℕ) :
    Disjoint (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (transSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, -, hil⟩ := mem_lowSet.mp h1
  have := (mem_transSet.mp h2).1
  simp only [Free] at this
  omega

theorem disj_up_fixlow (ρ : ℕ) :
    Disjoint (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ ∪ lowSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp h1
  rcases Finset.mem_union.mp h2 with h | h
  · rcases mem_fixSet.mp h with ⟨i', hq, -, hnf⟩ | ⟨l', s, -, -, hq⟩
    · exact hnf (by simp only [Free]; exact hli)
    · simp at hq
  · obtain ⟨l', i', he, -, hil⟩ := mem_lowSet.mp h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    omega

end Sets

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem kills_low (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ)) :
    ∀ j : ℕ, Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ (lowSet ρ).filter (fun e => colIx e < j))
      (transSet ρ) := by
  intro j
  induction j with
  | zero => simpa using K
  | succ j ih =>
    have hsplit : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < j + 1) =
        (lowSet ρ).filter (fun e => colIx e < j) ∪ (lowSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_evals ψ ν hψ hψ1 hν L chL _ (transSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_low_trans ρ)) ih ?_
    intro e he E' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hρi, hil⟩ := mem_lowSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_lower_entry_multiplication_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hρi hil E'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simpa [he2] using hx
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

theorem kills_up (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ)) :
    ∀ d j : ℕ, j + d = c + 1 → Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ)
      (transSet ρ ∪ (upSet ρ).filter (fun e => j ≤ colIx e)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hemp : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) = ∅ := by
      apply Finset.filter_false_of_mem
      intro e he
      obtain ⟨l, i, rfl, -, -⟩ := mem_upSet.mp he
      simp only [colIx, Sum.elim_inr]
      have := i.isLt
      omega
    rw [hemp, Finset.union_empty]
    exact K
  | succ d ih =>
    intro j hj
    have hsplit : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) =
        (upSet ρ).filter (fun e => j + 1 ≤ colIx e) ∪ (upSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_ints ψ ν hψ hν L chL _ (fixSet ρ ∪ lowSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_up_fixlow ρ)) (ih (j + 1) (by omega)) ?_
    intro e he I' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_upper_free_entry_translation_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hli hiρ I'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

end Main
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

theorem flRow_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  have K0 := kills_empty ψ ν L chL (basePt c (0 : Matrix n n' k))
  have K1 := kills_evals ψ ν hψ hψ1 hν L chL (basePt c (0 : Matrix n n' k)) ∅ (fixSet ρ) ∅
    (Finset.disjoint_empty_right _) K0 (by
      intro e he E' _ _ heE'
      refine evalLaw_direct ψ ν hψ L chL _ E' ∅ e (Finset.notMem_empty _) heE' ?_
      obtain ⟨r, q⟩ := e
      rcases mem_fixSet.mp he with h | h
      · exact H1 r q h
      · exact H2 r q h)
  rw [Finset.empty_union] at K1
  have K2 := kills_ints ψ ν hψ hν L chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ) ∅
    (disj_trans_fix ρ) K1 (by
      intro e he I' _ _ heI'
      refine intLaw_direct ψ ν L chL _ (fixSet ρ) I' e heI'
        (Finset.disjoint_left.mp (disj_trans_fix ρ) he) ?_
      obtain ⟨r, q⟩ := e
      have h := mem_transSet.mp he
      intro a Φ Φ' hΦ'
      rw [chL_apply]
      exact H3 r q h.1 h.2 a Φ Φ' hΦ')
  rw [Finset.empty_union] at K2
  have K3 := kills_low ψ ν hψ hψ1 hν ρ L hc H4 K2 (c + 1)
  have hlow : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < c + 1) = lowSet ρ := by
    apply Finset.filter_true_of_mem
    intro e he
    obtain ⟨l, i, rfl, -, -⟩ := mem_lowSet.mp he
    simp only [colIx, Sum.elim_inr]
    exact i.isLt
  rw [hlow] at K3
  have K4 := kills_up ψ ν hψ hν ρ L hc H4 K3 (c + 1) 0 (by omega)
  have hup : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => 0 ≤ colIx e) = upSet ρ := by
    apply Finset.filter_true_of_mem
    intro e _
    exact Nat.zero_le _
  rw [hup] at K4
  have hρc : ρ < c := by omega
  let lρ : Fin c := ⟨ρ, hρc⟩
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (Matrix (n ⊕ Unit) n' k → ℂ) :=
    { toFun := fun Φ => flRow ψ ν (ρ + 1) Φ.1
      map_add' := fun Φ₁ Φ₂ => GlobalTheory.T.flatMapFourierJacobiRow_add k ψ ν hψ hν n n' c (ρ + 1) Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2
      map_smul' := fun a Φ => by
        funext x
        simp only [flRow, opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hker : LinearMap.ker F ≤ LinearMap.ker L := by
    intro Φ hΦ
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply K4
    funext x
    rw [GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow k ψ ν hν n n' c ρ hc lρ rfl Φ.1 x]
    exact congrFun hΦ _
  let f₀ : LinearMap.range F →ₗ[ℂ] M := (LinearMap.ker F).liftQ L hker ∘ₗ F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
  refine ⟨g ∘ₗ (SB (Matrix (n ⊕ Unit) n' k)).subtype, fun Φ Ψ hΨ => ?_⟩
  have h1 : g (F Φ) = L Φ := by
    have := LinearMap.congr_fun hg ⟨F Φ, LinearMap.mem_range_self F Φ⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  rw [LinearMap.comp_apply, Submodule.coe_subtype, hΨ]
  exact h1.symm

end GlobalTheory.PartRed
